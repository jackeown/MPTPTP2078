%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 131 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 351 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f85])).

fof(f85,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f84,f81])).

fof(f81,plain,(
    r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f80,f28])).

fof(f28,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f80,plain,(
    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f64,plain,(
    v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f36,f38])).

fof(f38,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f36,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f33,plain,(
    m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(sK3)) ),
    inference(resolution,[],[f20,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f20,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)) ),
    inference(resolution,[],[f49,f20])).

fof(f49,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | ~ v1_relat_1(X3)
      | r1_tarski(k2_relat_1(X3),k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f84,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_relat_1(sK3)))
    | ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(resolution,[],[f67,f23])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_relat_1(sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_relat_1(sK3))) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(resolution,[],[f44,f24])).

fof(f44,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f43,f40])).

fof(f40,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f19,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f43,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f18,f39])).

fof(f39,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f19,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f18,plain,
    ( ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_relat_1(sK3))) ),
    inference(resolution,[],[f74,f23])).

fof(f74,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f73,f27])).

fof(f27,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f71,f64])).

fof(f71,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) ),
    inference(resolution,[],[f47,f20])).

fof(f47,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK3)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (23854)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.47  % (23870)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.48  % (23870)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_relat_1(sK3)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.48    inference(forward_demodulation,[],[f80,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3))),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_relat_1(k6_relat_1(sK2))),
% 0.21/0.48    inference(resolution,[],[f36,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f19,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~v1_relat_1(sK3) | v1_relat_1(k6_relat_1(sK2))),
% 0.21/0.48    inference(resolution,[],[f33,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(sK3))),
% 0.21/0.48    inference(resolution,[],[f20,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r1_tarski(k6_relat_1(sK2),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~v1_relat_1(k6_relat_1(sK2)) | r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3))),
% 0.21/0.48    inference(resolution,[],[f49,f20])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X3] : (~r1_tarski(X3,sK3) | ~v1_relat_1(X3) | r1_tarski(k2_relat_1(X3),k2_relat_1(sK3))) )),
% 0.21/0.48    inference(resolution,[],[f38,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_relat_1(sK3))) | ~r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.48    inference(resolution,[],[f67,f23])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_relat_1(sK3))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_relat_1(sK3)))),
% 0.21/0.48    inference(resolution,[],[f45,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_relat_1(sK3)))),
% 0.21/0.48    inference(resolution,[],[f44,f24])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~r1_tarski(sK2,k2_relat_1(sK3)) | ~r1_tarski(sK2,k1_relat_1(sK3))),
% 0.21/0.48    inference(backward_demodulation,[],[f43,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f19,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.48    inference(backward_demodulation,[],[f18,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f19,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_relat_1(sK3)))),
% 0.21/0.48    inference(resolution,[],[f74,f23])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    r1_tarski(sK2,k1_relat_1(sK3))),
% 0.21/0.48    inference(forward_demodulation,[],[f73,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))),
% 0.21/0.48    inference(subsumption_resolution,[],[f71,f64])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~v1_relat_1(k6_relat_1(sK2)) | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))),
% 0.21/0.48    inference(resolution,[],[f47,f20])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,sK3) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),k1_relat_1(sK3))) )),
% 0.21/0.48    inference(resolution,[],[f38,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (23870)------------------------------
% 0.21/0.48  % (23870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23870)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (23870)Memory used [KB]: 1663
% 0.21/0.48  % (23870)Time elapsed: 0.065 s
% 0.21/0.48  % (23870)------------------------------
% 0.21/0.48  % (23870)------------------------------
% 0.21/0.48  % (23848)Success in time 0.126 s
%------------------------------------------------------------------------------
