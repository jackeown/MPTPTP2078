%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:36 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  82 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   17
%              Number of atoms          :  121 ( 281 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(resolution,[],[f53,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f53,plain,(
    ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f52,f19])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

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

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f50,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f50,plain,(
    ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f49,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f49,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3) ),
    inference(global_subsumption,[],[f20,f48])).

fof(f48,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(k6_relat_1(sK2),sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(X1))
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f46,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3) ),
    inference(global_subsumption,[],[f20,f44])).

fof(f44,plain,
    ( ~ r1_tarski(k6_relat_1(sK2),sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f38,f36])).

fof(f36,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f30,f19])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f38,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(superposition,[],[f21,f37])).

fof(f37,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f31,f19])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f21,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f27,f25])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : run_vampire %s %d
% 0.08/0.28  % Computer   : n015.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 11:52:38 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.14/0.34  % (4773)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.14/0.34  % (4766)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.14/0.34  % (4768)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.34  % (4769)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.14/0.34  % (4766)Refutation found. Thanks to Tanya!
% 0.14/0.34  % SZS status Theorem for theBenchmark
% 0.14/0.34  % SZS output start Proof for theBenchmark
% 0.14/0.34  fof(f54,plain,(
% 0.14/0.34    $false),
% 0.14/0.34    inference(resolution,[],[f53,f29])).
% 0.14/0.35  fof(f29,plain,(
% 0.14/0.35    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.14/0.35    inference(cnf_transformation,[],[f2])).
% 0.14/0.35  fof(f2,axiom,(
% 0.14/0.35    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.14/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.14/0.35  fof(f53,plain,(
% 0.14/0.35    ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.14/0.35    inference(resolution,[],[f52,f19])).
% 0.14/0.35  fof(f19,plain,(
% 0.14/0.35    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.14/0.35    inference(cnf_transformation,[],[f18])).
% 0.14/0.35  fof(f18,plain,(
% 0.14/0.35    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.14/0.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).
% 0.14/0.35  fof(f17,plain,(
% 0.14/0.35    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.14/0.35    introduced(choice_axiom,[])).
% 0.14/0.35  fof(f11,plain,(
% 0.14/0.35    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.14/0.35    inference(flattening,[],[f10])).
% 0.14/0.35  fof(f10,plain,(
% 0.14/0.35    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.14/0.35    inference(ennf_transformation,[],[f9])).
% 0.14/0.35  fof(f9,negated_conjecture,(
% 0.14/0.35    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.14/0.35    inference(negated_conjecture,[],[f8])).
% 0.14/0.35  fof(f8,conjecture,(
% 0.14/0.35    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.14/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.14/0.35  fof(f52,plain,(
% 0.14/0.35    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.14/0.35    inference(resolution,[],[f50,f28])).
% 0.14/0.35  fof(f28,plain,(
% 0.14/0.35    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.14/0.35    inference(cnf_transformation,[],[f14])).
% 0.14/0.35  fof(f14,plain,(
% 0.14/0.35    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.14/0.35    inference(ennf_transformation,[],[f1])).
% 0.14/0.35  fof(f1,axiom,(
% 0.14/0.35    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.14/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.14/0.35  fof(f50,plain,(
% 0.14/0.35    ~v1_relat_1(sK3)),
% 0.14/0.35    inference(resolution,[],[f49,f22])).
% 0.14/0.35  fof(f22,plain,(
% 0.14/0.35    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.35    inference(cnf_transformation,[],[f5])).
% 0.14/0.35  fof(f5,axiom,(
% 0.14/0.35    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.14/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.14/0.35  fof(f49,plain,(
% 0.14/0.35    ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(sK3)),
% 0.14/0.35    inference(global_subsumption,[],[f20,f48])).
% 0.14/0.35  fof(f48,plain,(
% 0.14/0.35    ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(sK3) | ~r1_tarski(k6_relat_1(sK2),sK3)),
% 0.14/0.35    inference(duplicate_literal_removal,[],[f47])).
% 0.14/0.35  fof(f47,plain,(
% 0.14/0.35    ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(sK3) | ~r1_tarski(k6_relat_1(sK2),sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK2))),
% 0.14/0.35    inference(resolution,[],[f46,f32])).
% 0.14/0.35  fof(f32,plain,(
% 0.14/0.35    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.35    inference(superposition,[],[f26,f24])).
% 0.14/0.35  fof(f24,plain,(
% 0.14/0.35    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.14/0.35    inference(cnf_transformation,[],[f4])).
% 0.14/0.35  fof(f4,axiom,(
% 0.14/0.35    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.14/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.14/0.35  fof(f26,plain,(
% 0.14/0.35    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.14/0.35    inference(cnf_transformation,[],[f13])).
% 0.14/0.35  fof(f13,plain,(
% 0.14/0.35    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.14/0.35    inference(flattening,[],[f12])).
% 0.14/0.35  fof(f12,plain,(
% 0.14/0.35    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.14/0.35    inference(ennf_transformation,[],[f3])).
% 0.14/0.35  fof(f3,axiom,(
% 0.14/0.35    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.14/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.14/0.35  fof(f46,plain,(
% 0.14/0.35    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(sK3)),
% 0.14/0.35    inference(global_subsumption,[],[f20,f44])).
% 0.14/0.35  fof(f44,plain,(
% 0.14/0.35    ~r1_tarski(k6_relat_1(sK2),sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK2)) | ~r1_tarski(sK2,k1_relat_1(sK3))),
% 0.14/0.35    inference(resolution,[],[f34,f39])).
% 0.14/0.35  fof(f39,plain,(
% 0.14/0.35    ~r1_tarski(sK2,k2_relat_1(sK3)) | ~r1_tarski(sK2,k1_relat_1(sK3))),
% 0.14/0.35    inference(forward_demodulation,[],[f38,f36])).
% 0.14/0.35  fof(f36,plain,(
% 0.14/0.35    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.14/0.35    inference(resolution,[],[f30,f19])).
% 0.14/0.35  fof(f30,plain,(
% 0.14/0.35    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.14/0.35    inference(cnf_transformation,[],[f15])).
% 0.14/0.35  fof(f15,plain,(
% 0.14/0.35    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.14/0.35    inference(ennf_transformation,[],[f6])).
% 0.14/0.35  fof(f6,axiom,(
% 0.14/0.35    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.14/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.14/0.35  fof(f38,plain,(
% 0.14/0.35    ~r1_tarski(sK2,k2_relat_1(sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.14/0.35    inference(superposition,[],[f21,f37])).
% 0.14/0.35  fof(f37,plain,(
% 0.14/0.35    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.14/0.35    inference(resolution,[],[f31,f19])).
% 0.14/0.35  fof(f31,plain,(
% 0.14/0.35    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.14/0.35    inference(cnf_transformation,[],[f16])).
% 0.14/0.35  fof(f16,plain,(
% 0.14/0.35    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.14/0.35    inference(ennf_transformation,[],[f7])).
% 0.14/0.35  fof(f7,axiom,(
% 0.14/0.35    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.14/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.14/0.35  fof(f21,plain,(
% 0.14/0.35    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.14/0.35    inference(cnf_transformation,[],[f18])).
% 0.14/0.35  fof(f34,plain,(
% 0.14/0.35    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.35    inference(superposition,[],[f27,f25])).
% 0.14/0.35  fof(f25,plain,(
% 0.14/0.35    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.14/0.35    inference(cnf_transformation,[],[f4])).
% 0.14/0.35  fof(f27,plain,(
% 0.14/0.35    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.14/0.35    inference(cnf_transformation,[],[f13])).
% 0.14/0.35  fof(f20,plain,(
% 0.14/0.35    r1_tarski(k6_relat_1(sK2),sK3)),
% 0.14/0.35    inference(cnf_transformation,[],[f18])).
% 0.14/0.35  % SZS output end Proof for theBenchmark
% 0.14/0.35  % (4766)------------------------------
% 0.14/0.35  % (4766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.35  % (4766)Termination reason: Refutation
% 0.14/0.35  
% 0.14/0.35  % (4766)Memory used [KB]: 6140
% 0.14/0.35  % (4766)Time elapsed: 0.004 s
% 0.14/0.35  % (4766)------------------------------
% 0.14/0.35  % (4766)------------------------------
% 0.14/0.35  % (4767)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.35  % (4761)Success in time 0.058 s
%------------------------------------------------------------------------------
