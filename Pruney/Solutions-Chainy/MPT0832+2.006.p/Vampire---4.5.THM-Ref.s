%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 100 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   19
%              Number of atoms          :  139 ( 234 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f81])).

% (4570)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f81,plain,(
    ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    inference(resolution,[],[f79,f28])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f78,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(sK3,X1)
      | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f74,f28])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK3)
      | ~ v4_relat_1(sK3,X1)
      | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f71,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f70,f28])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ r1_tarski(k1_relat_1(sK3),X1)
      | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f67,f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK3)
      | m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f58,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

fof(f58,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X3,sK3)),X5)
      | ~ r1_tarski(X5,X4)
      | m1_subset_1(k8_relat_1(X3,sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),X1)
      | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f54,f28])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),X1) ) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),X1)
      | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X2)
      | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),X1) ) ),
    inference(resolution,[],[f49,f28])).

fof(f49,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | m1_subset_1(k8_relat_1(X5,X6),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(X5,X6)),X8)
      | ~ r1_tarski(k1_relat_1(k8_relat_1(X5,X6)),X7) ) ),
    inference(resolution,[],[f42,f36])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X3)
      | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X2) ) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f41,plain,(
    ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(backward_demodulation,[],[f29,f40])).

fof(f40,plain,(
    ! [X0] : k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3) ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

% (4563)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f29,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:16:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (4568)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.46  % (4580)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.46  % (4568)Refutation not found, incomplete strategy% (4568)------------------------------
% 0.19/0.46  % (4568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (4568)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (4568)Memory used [KB]: 10618
% 0.19/0.46  % (4568)Time elapsed: 0.056 s
% 0.19/0.46  % (4568)------------------------------
% 0.19/0.46  % (4568)------------------------------
% 0.19/0.47  % (4564)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.47  % (4571)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.48  % (4573)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.48  % (4581)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.48  % (4578)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.48  % (4578)Refutation not found, incomplete strategy% (4578)------------------------------
% 0.19/0.48  % (4578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (4578)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (4578)Memory used [KB]: 1535
% 0.19/0.48  % (4578)Time elapsed: 0.089 s
% 0.19/0.48  % (4578)------------------------------
% 0.19/0.48  % (4578)------------------------------
% 0.19/0.48  % (4581)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(subsumption_resolution,[],[f41,f81])).
% 0.19/0.48  % (4570)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) )),
% 0.19/0.49    inference(resolution,[],[f79,f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.19/0.49    inference(negated_conjecture,[],[f10])).
% 0.19/0.49  fof(f10,conjecture,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.49    inference(resolution,[],[f78,f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v4_relat_1(sK3,X1) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.49    inference(resolution,[],[f74,f28])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v4_relat_1(sK3,X0)) )),
% 0.19/0.49    inference(resolution,[],[f72,f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_relat_1(sK3) | ~v4_relat_1(sK3,X1) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.49    inference(resolution,[],[f71,f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(resolution,[],[f70,f28])).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k1_relat_1(sK3),X1) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.49    inference(resolution,[],[f67,f36])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_relat_1(sK3) | m1_subset_1(k8_relat_1(X1,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(sK3),X0)) )),
% 0.19/0.49    inference(resolution,[],[f58,f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    ( ! [X4,X5,X3] : (~r1_tarski(k1_relat_1(k8_relat_1(X3,sK3)),X5) | ~r1_tarski(X5,X4) | m1_subset_1(k8_relat_1(X3,sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))) )),
% 0.19/0.49    inference(resolution,[],[f55,f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(flattening,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),X1) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.49    inference(resolution,[],[f54,f28])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),X1)) )),
% 0.19/0.49    inference(resolution,[],[f52,f36])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_relat_1(sK3) | ~r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),X1) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.19/0.49    inference(resolution,[],[f51,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X2) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),X1)) )),
% 0.19/0.49    inference(resolution,[],[f49,f28])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ( ! [X6,X10,X8,X7,X5,X9] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | m1_subset_1(k8_relat_1(X5,X6),k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~r1_tarski(k2_relat_1(k8_relat_1(X5,X6)),X8) | ~r1_tarski(k1_relat_1(k8_relat_1(X5,X6)),X7)) )),
% 0.19/0.49    inference(resolution,[],[f42,f36])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X3) | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X2)) )),
% 0.19/0.49    inference(resolution,[],[f35,f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(flattening,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.19/0.49    inference(backward_demodulation,[],[f29,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0] : (k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)) )),
% 0.19/0.49    inference(resolution,[],[f39,f28])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  % (4563)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (4581)------------------------------
% 0.19/0.49  % (4581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (4581)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (4581)Memory used [KB]: 6140
% 0.19/0.49  % (4581)Time elapsed: 0.082 s
% 0.19/0.49  % (4581)------------------------------
% 0.19/0.49  % (4581)------------------------------
% 0.19/0.49  % (4561)Success in time 0.146 s
%------------------------------------------------------------------------------
