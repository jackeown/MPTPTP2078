%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:07 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 113 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 300 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f41])).

fof(f41,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

fof(f70,plain,(
    ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(backward_demodulation,[],[f46,f69])).

fof(f69,plain,(
    sK3 = k8_relat_1(sK2,sK3) ),
    inference(backward_demodulation,[],[f64,f68])).

fof(f68,plain,(
    sK3 = k8_relat_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f66,f47])).

fof(f47,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f45,f30])).

fof(f30,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f45,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f66,plain,
    ( sK3 = k8_relat_1(sK1,sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f57,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f57,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f56,f47])).

fof(f56,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f44,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f64,plain,(
    k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3)) ),
    inference(resolution,[],[f40,f47])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(sK1,X0) = k8_relat_1(sK2,k8_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ~ r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) ),
    inference(backward_demodulation,[],[f28,f42])).

fof(f42,plain,(
    ! [X0] : k6_relset_1(sK0,sK1,X0,sK3) = k8_relat_1(X0,sK3) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f28,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : run_vampire %s %d
% 0.06/0.26  % Computer   : n006.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 20:10:22 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.11/0.33  % (10040)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.11/0.33  % (10037)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.11/0.33  % (10038)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.11/0.34  % (10036)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.11/0.34  % (10039)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.11/0.34  % (10047)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.11/0.34  % (10047)Refutation found. Thanks to Tanya!
% 0.11/0.34  % SZS status Theorem for theBenchmark
% 0.11/0.34  % SZS output start Proof for theBenchmark
% 0.11/0.34  fof(f71,plain,(
% 0.11/0.34    $false),
% 0.11/0.34    inference(subsumption_resolution,[],[f70,f41])).
% 0.11/0.34  fof(f41,plain,(
% 0.11/0.34    r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.11/0.34    inference(resolution,[],[f26,f39])).
% 0.11/0.34  fof(f39,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.11/0.34    inference(condensation,[],[f38])).
% 0.11/0.34  fof(f38,plain,(
% 0.11/0.34    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.34    inference(cnf_transformation,[],[f22])).
% 0.11/0.34  fof(f22,plain,(
% 0.11/0.34    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.34    inference(flattening,[],[f21])).
% 0.11/0.34  fof(f21,plain,(
% 0.11/0.34    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.11/0.34    inference(ennf_transformation,[],[f8])).
% 0.11/0.34  fof(f8,axiom,(
% 0.11/0.34    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.11/0.34  fof(f26,plain,(
% 0.11/0.34    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.34    inference(cnf_transformation,[],[f24])).
% 0.11/0.34  fof(f24,plain,(
% 0.11/0.34    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.34    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23])).
% 0.11/0.34  fof(f23,plain,(
% 0.11/0.34    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.11/0.34    introduced(choice_axiom,[])).
% 0.11/0.34  fof(f12,plain,(
% 0.11/0.34    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.34    inference(flattening,[],[f11])).
% 0.11/0.34  fof(f11,plain,(
% 0.11/0.34    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.34    inference(ennf_transformation,[],[f10])).
% 0.11/0.34  fof(f10,negated_conjecture,(
% 0.11/0.34    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 0.11/0.34    inference(negated_conjecture,[],[f9])).
% 0.11/0.34  fof(f9,conjecture,(
% 0.11/0.34    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).
% 0.11/0.34  fof(f70,plain,(
% 0.11/0.34    ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.11/0.34    inference(backward_demodulation,[],[f46,f69])).
% 0.11/0.34  fof(f69,plain,(
% 0.11/0.34    sK3 = k8_relat_1(sK2,sK3)),
% 0.11/0.34    inference(backward_demodulation,[],[f64,f68])).
% 0.11/0.34  fof(f68,plain,(
% 0.11/0.34    sK3 = k8_relat_1(sK1,sK3)),
% 0.11/0.34    inference(subsumption_resolution,[],[f66,f47])).
% 0.11/0.34  fof(f47,plain,(
% 0.11/0.34    v1_relat_1(sK3)),
% 0.11/0.34    inference(subsumption_resolution,[],[f45,f30])).
% 0.11/0.34  fof(f30,plain,(
% 0.11/0.34    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.11/0.34    inference(cnf_transformation,[],[f3])).
% 0.11/0.34  fof(f3,axiom,(
% 0.11/0.34    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.11/0.34  fof(f45,plain,(
% 0.11/0.34    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.11/0.34    inference(resolution,[],[f26,f29])).
% 0.11/0.34  fof(f29,plain,(
% 0.11/0.34    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.11/0.34    inference(cnf_transformation,[],[f13])).
% 0.11/0.34  fof(f13,plain,(
% 0.11/0.34    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.11/0.34    inference(ennf_transformation,[],[f1])).
% 0.11/0.34  fof(f1,axiom,(
% 0.11/0.34    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.11/0.34  fof(f66,plain,(
% 0.11/0.34    sK3 = k8_relat_1(sK1,sK3) | ~v1_relat_1(sK3)),
% 0.11/0.34    inference(resolution,[],[f57,f31])).
% 0.11/0.34  fof(f31,plain,(
% 0.11/0.34    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.11/0.34    inference(cnf_transformation,[],[f15])).
% 0.11/0.34  fof(f15,plain,(
% 0.11/0.34    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.11/0.34    inference(flattening,[],[f14])).
% 0.11/0.34  fof(f14,plain,(
% 0.11/0.34    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.11/0.34    inference(ennf_transformation,[],[f4])).
% 0.11/0.34  fof(f4,axiom,(
% 0.11/0.34    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.11/0.34  fof(f57,plain,(
% 0.11/0.34    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.11/0.34    inference(subsumption_resolution,[],[f56,f47])).
% 0.11/0.34  fof(f56,plain,(
% 0.11/0.34    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 0.11/0.34    inference(resolution,[],[f44,f32])).
% 0.11/0.34  fof(f32,plain,(
% 0.11/0.34    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.11/0.34    inference(cnf_transformation,[],[f25])).
% 0.11/0.34  fof(f25,plain,(
% 0.11/0.34    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.11/0.34    inference(nnf_transformation,[],[f16])).
% 0.11/0.34  fof(f16,plain,(
% 0.11/0.34    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.11/0.34    inference(ennf_transformation,[],[f2])).
% 0.11/0.34  fof(f2,axiom,(
% 0.11/0.34    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.11/0.34  fof(f44,plain,(
% 0.11/0.34    v5_relat_1(sK3,sK1)),
% 0.11/0.34    inference(resolution,[],[f26,f36])).
% 0.11/0.34  fof(f36,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.34    inference(cnf_transformation,[],[f19])).
% 0.11/0.34  fof(f19,plain,(
% 0.11/0.34    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.34    inference(ennf_transformation,[],[f6])).
% 0.11/0.34  fof(f6,axiom,(
% 0.11/0.34    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.11/0.34  fof(f64,plain,(
% 0.11/0.34    k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3))),
% 0.11/0.34    inference(resolution,[],[f40,f47])).
% 0.11/0.34  fof(f40,plain,(
% 0.11/0.34    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(sK1,X0) = k8_relat_1(sK2,k8_relat_1(sK1,X0))) )),
% 0.11/0.34    inference(resolution,[],[f27,f34])).
% 0.11/0.34  fof(f34,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.11/0.34    inference(cnf_transformation,[],[f18])).
% 0.11/0.34  fof(f18,plain,(
% 0.11/0.34    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.11/0.34    inference(flattening,[],[f17])).
% 0.11/0.34  fof(f17,plain,(
% 0.11/0.34    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.11/0.34    inference(ennf_transformation,[],[f5])).
% 0.11/0.34  fof(f5,axiom,(
% 0.11/0.34    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 0.11/0.34  fof(f27,plain,(
% 0.11/0.34    r1_tarski(sK1,sK2)),
% 0.11/0.34    inference(cnf_transformation,[],[f24])).
% 0.11/0.34  fof(f46,plain,(
% 0.11/0.34    ~r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)),
% 0.11/0.34    inference(backward_demodulation,[],[f28,f42])).
% 0.11/0.34  fof(f42,plain,(
% 0.11/0.34    ( ! [X0] : (k6_relset_1(sK0,sK1,X0,sK3) = k8_relat_1(X0,sK3)) )),
% 0.11/0.34    inference(resolution,[],[f26,f37])).
% 0.11/0.34  fof(f37,plain,(
% 0.11/0.34    ( ! [X2,X0,X3,X1] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.34    inference(cnf_transformation,[],[f20])).
% 0.11/0.34  fof(f20,plain,(
% 0.11/0.34    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.34    inference(ennf_transformation,[],[f7])).
% 0.11/0.34  fof(f7,axiom,(
% 0.11/0.34    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.11/0.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.11/0.34  fof(f28,plain,(
% 0.11/0.34    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 0.11/0.34    inference(cnf_transformation,[],[f24])).
% 0.11/0.34  % SZS output end Proof for theBenchmark
% 0.11/0.34  % (10047)------------------------------
% 0.11/0.34  % (10047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.34  % (10047)Termination reason: Refutation
% 0.11/0.34  
% 0.11/0.34  % (10047)Memory used [KB]: 1663
% 0.11/0.34  % (10047)Time elapsed: 0.049 s
% 0.11/0.34  % (10047)------------------------------
% 0.11/0.34  % (10047)------------------------------
% 0.11/0.34  % (10039)Refutation not found, incomplete strategy% (10039)------------------------------
% 0.11/0.34  % (10039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.34  % (10039)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.34  
% 0.11/0.34  % (10039)Memory used [KB]: 10490
% 0.11/0.34  % (10039)Time elapsed: 0.050 s
% 0.11/0.34  % (10039)------------------------------
% 0.11/0.34  % (10039)------------------------------
% 0.11/0.35  % (10052)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.11/0.35  % (10051)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.11/0.35  % (10046)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.11/0.35  % (10054)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.11/0.35  % (10052)Refutation not found, incomplete strategy% (10052)------------------------------
% 0.11/0.35  % (10052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.35  % (10046)Refutation not found, incomplete strategy% (10046)------------------------------
% 0.11/0.35  % (10046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.35  % (10052)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.35  
% 0.11/0.35  % (10052)Memory used [KB]: 1663
% 0.11/0.35  % (10052)Time elapsed: 0.051 s
% 0.11/0.35  % (10052)------------------------------
% 0.11/0.35  % (10052)------------------------------
% 0.11/0.35  % (10046)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.35  
% 0.11/0.35  % (10046)Memory used [KB]: 10618
% 0.11/0.35  % (10046)Time elapsed: 0.054 s
% 0.11/0.35  % (10046)------------------------------
% 0.11/0.35  % (10046)------------------------------
% 0.11/0.35  % (10057)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.11/0.35  % (10042)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.11/0.36  % (10035)Success in time 0.091 s
%------------------------------------------------------------------------------
