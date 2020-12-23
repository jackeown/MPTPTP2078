%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:03 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 103 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 232 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(resolution,[],[f250,f54])).

fof(f54,plain,(
    r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f53,f45])).

fof(f45,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f44,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f32,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f53,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(superposition,[],[f36,f52])).

fof(f52,plain,(
    sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f51,f45])).

fof(f51,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f40,f30])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f250,plain,(
    ~ r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f245,f45])).

fof(f245,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f129,f56])).

fof(f56,plain,(
    ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(backward_demodulation,[],[f31,f55])).

fof(f55,plain,(
    ! [X0] : k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3) ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,(
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

fof(f31,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f78,f50])).

fof(f50,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X8,X6)),X7)
      | ~ r1_tarski(k1_relat_1(X6),X7)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2)
      | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2)
      | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f59,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2)
      | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.47  % (30350)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.23/0.48  % (30358)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.49  % (30351)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.23/0.49  % (30350)Refutation not found, incomplete strategy% (30350)------------------------------
% 0.23/0.49  % (30350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (30350)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (30350)Memory used [KB]: 10490
% 0.23/0.49  % (30350)Time elapsed: 0.069 s
% 0.23/0.49  % (30350)------------------------------
% 0.23/0.49  % (30350)------------------------------
% 0.23/0.50  % (30349)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.50  % (30349)Refutation not found, incomplete strategy% (30349)------------------------------
% 0.23/0.50  % (30349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (30349)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (30349)Memory used [KB]: 6140
% 0.23/0.50  % (30349)Time elapsed: 0.064 s
% 0.23/0.50  % (30349)------------------------------
% 0.23/0.50  % (30349)------------------------------
% 0.23/0.50  % (30351)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f251,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(resolution,[],[f250,f54])).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    r1_tarski(k1_relat_1(sK3),sK2)),
% 0.23/0.50    inference(resolution,[],[f53,f45])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    v1_relat_1(sK3)),
% 0.23/0.50    inference(resolution,[],[f44,f33])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.23/0.50  fof(f44,plain,(
% 0.23/0.50    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | v1_relat_1(sK3)),
% 0.23/0.50    inference(resolution,[],[f32,f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.23/0.50    inference(cnf_transformation,[],[f29])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f28])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.23/0.50    inference(ennf_transformation,[],[f13])).
% 0.23/0.50  fof(f13,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.23/0.50    inference(negated_conjecture,[],[f12])).
% 0.23/0.50  fof(f12,conjecture,(
% 0.23/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    ~v1_relat_1(sK3) | r1_tarski(k1_relat_1(sK3),sK2)),
% 0.23/0.51    inference(superposition,[],[f36,f52])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    sK3 = k7_relat_1(sK3,sK2)),
% 0.23/0.51    inference(resolution,[],[f51,f45])).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK2)),
% 0.23/0.51    inference(resolution,[],[f38,f46])).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    v4_relat_1(sK3,sK2)),
% 0.23/0.51    inference(resolution,[],[f40,f30])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(flattening,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.23/0.51  fof(f250,plain,(
% 0.23/0.51    ~r1_tarski(k1_relat_1(sK3),sK2)),
% 0.23/0.51    inference(resolution,[],[f245,f45])).
% 0.23/0.51  fof(f245,plain,(
% 0.23/0.51    ~v1_relat_1(sK3) | ~r1_tarski(k1_relat_1(sK3),sK2)),
% 0.23/0.51    inference(resolution,[],[f129,f56])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.23/0.51    inference(backward_demodulation,[],[f31,f55])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    ( ! [X0] : (k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)) )),
% 0.23/0.51    inference(resolution,[],[f43,f30])).
% 0.23/0.51  fof(f43,plain,(
% 0.23/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,axiom,(
% 0.23/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.23/0.51    inference(cnf_transformation,[],[f29])).
% 0.23/0.51  fof(f129,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X2)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f126])).
% 0.23/0.51  fof(f126,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X2) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(resolution,[],[f78,f50])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ( ! [X6,X8,X7] : (r1_tarski(k1_relat_1(k8_relat_1(X8,X6)),X7) | ~r1_tarski(k1_relat_1(X6),X7) | ~v1_relat_1(X6)) )),
% 0.23/0.51    inference(resolution,[],[f42,f37])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(flattening,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.23/0.51  fof(f78,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2) | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f77])).
% 0.23/0.51  fof(f77,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2) | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_relat_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(resolution,[],[f59,f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(k8_relat_1(X0,X1)) | ~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2) | m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(resolution,[],[f39,f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.23/0.51    inference(flattening,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.23/0.51    inference(ennf_transformation,[],[f11])).
% 0.23/0.51  fof(f11,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (30351)------------------------------
% 0.23/0.51  % (30351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (30351)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (30351)Memory used [KB]: 1918
% 0.23/0.51  % (30351)Time elapsed: 0.076 s
% 0.23/0.51  % (30351)------------------------------
% 0.23/0.51  % (30351)------------------------------
% 0.23/0.51  % (30357)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.23/0.51  % (30346)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.52  % (30361)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.23/0.52  % (30352)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.23/0.52  % (30352)Refutation not found, incomplete strategy% (30352)------------------------------
% 0.23/0.52  % (30352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (30352)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (30352)Memory used [KB]: 10618
% 0.23/0.52  % (30352)Time elapsed: 0.114 s
% 0.23/0.52  % (30352)------------------------------
% 0.23/0.52  % (30352)------------------------------
% 0.23/0.52  % (30364)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.23/0.53  % (30342)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.23/0.53  % (30341)Success in time 0.162 s
%------------------------------------------------------------------------------
