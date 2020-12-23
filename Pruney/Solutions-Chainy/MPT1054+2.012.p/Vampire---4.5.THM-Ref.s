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
% DateTime   : Thu Dec  3 13:07:07 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   55 (  66 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 156 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f78,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f78,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f68,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X1),X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f65,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k10_relat_1(k6_relat_1(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(X1,k10_relat_1(k6_relat_1(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f56,f34])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k10_relat_1(k6_relat_1(X0),X1))
      | ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f55,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k10_relat_1(k6_relat_1(X0),X1))
      | ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k10_relat_1(k6_relat_1(X1),X0) = X0
      | ~ r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X0)) ) ),
    inference(resolution,[],[f64,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f31,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f61,f33])).

fof(f33,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f68,plain,(
    sK1 != k10_relat_1(k6_relat_1(sK0),sK1) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f67,plain,
    ( sK1 != k10_relat_1(k6_relat_1(sK0),sK1)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f47,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f47,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f27,f28])).

fof(f28,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f27,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (12062)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (12079)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (12071)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (12067)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (12071)Refutation not found, incomplete strategy% (12071)------------------------------
% 0.22/0.54  % (12071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12071)Memory used [KB]: 10618
% 0.22/0.54  % (12071)Time elapsed: 0.119 s
% 0.22/0.54  % (12071)------------------------------
% 0.22/0.54  % (12071)------------------------------
% 1.35/0.54  % (12059)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.35/0.54  % (12068)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.54  % (12063)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.54  % (12068)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f81,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(subsumption_resolution,[],[f78,f26])).
% 1.35/0.54  fof(f26,plain,(
% 1.35/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.54    inference(cnf_transformation,[],[f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).
% 1.35/0.54  fof(f21,plain,(
% 1.35/0.54    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f14,plain,(
% 1.35/0.54    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f13])).
% 1.35/0.54  fof(f13,negated_conjecture,(
% 1.35/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.35/0.54    inference(negated_conjecture,[],[f12])).
% 1.35/0.54  fof(f12,conjecture,(
% 1.35/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 1.35/0.54  fof(f78,plain,(
% 1.35/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.54    inference(trivial_inequality_removal,[],[f74])).
% 1.35/0.54  fof(f74,plain,(
% 1.35/0.54    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.54    inference(superposition,[],[f68,f66])).
% 1.35/0.54  fof(f66,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X1),X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f65,f58])).
% 1.35/0.54  fof(f58,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(X1,k10_relat_1(k6_relat_1(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f57,f42])).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f25])).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.35/0.54    inference(nnf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.35/0.54  fof(f57,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(X1,k10_relat_1(k6_relat_1(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(forward_demodulation,[],[f56,f34])).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.35/0.54  fof(f56,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(X1,k10_relat_1(k6_relat_1(X0),X1)) | ~r1_tarski(X1,k1_relat_1(k6_relat_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f55,f30])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.35/0.54  fof(f55,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(X1,k10_relat_1(k6_relat_1(X0),X1)) | ~r1_tarski(X1,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(superposition,[],[f36,f37])).
% 1.35/0.54  fof(f37,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f17])).
% 1.35/0.54  fof(f17,plain,(
% 1.35/0.54    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,axiom,(
% 1.35/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f16])).
% 1.35/0.54  fof(f16,plain,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.35/0.54    inference(flattening,[],[f15])).
% 1.35/0.54  fof(f15,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.35/0.54  fof(f65,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k10_relat_1(k6_relat_1(X1),X0) = X0 | ~r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X0))) )),
% 1.35/0.54    inference(resolution,[],[f64,f41])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.54    inference(flattening,[],[f23])).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.54    inference(nnf_transformation,[],[f1])).
% 1.35/0.54  fof(f1,axiom,(
% 1.35/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.35/0.54  fof(f64,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f63,f30])).
% 1.35/0.54  fof(f63,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(k6_relat_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f62,f31])).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f4])).
% 1.35/0.54  fof(f62,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f61,f33])).
% 1.35/0.54  fof(f33,plain,(
% 1.35/0.54    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f5])).
% 1.35/0.54  fof(f5,axiom,(
% 1.35/0.54    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.35/0.54  fof(f61,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X1) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(superposition,[],[f38,f37])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.35/0.54    inference(flattening,[],[f18])).
% 1.35/0.54  fof(f18,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.35/0.54    inference(ennf_transformation,[],[f7])).
% 1.35/0.54  fof(f7,axiom,(
% 1.35/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.35/0.54  fof(f68,plain,(
% 1.35/0.54    sK1 != k10_relat_1(k6_relat_1(sK0),sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f67,f29])).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.35/0.54  fof(f67,plain,(
% 1.35/0.54    sK1 != k10_relat_1(k6_relat_1(sK0),sK1) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.35/0.54    inference(superposition,[],[f47,f44])).
% 1.35/0.54  fof(f44,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f20])).
% 1.35/0.54  fof(f20,plain,(
% 1.35/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.54    inference(ennf_transformation,[],[f9])).
% 1.35/0.54  fof(f9,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 1.35/0.54    inference(forward_demodulation,[],[f27,f28])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f11])).
% 1.35/0.54  fof(f11,axiom,(
% 1.35/0.54    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f22])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (12068)------------------------------
% 1.35/0.54  % (12068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (12068)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (12068)Memory used [KB]: 1663
% 1.35/0.54  % (12068)Time elapsed: 0.123 s
% 1.35/0.54  % (12068)------------------------------
% 1.35/0.54  % (12068)------------------------------
% 1.35/0.54  % (12083)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.54  % (12058)Success in time 0.177 s
%------------------------------------------------------------------------------
