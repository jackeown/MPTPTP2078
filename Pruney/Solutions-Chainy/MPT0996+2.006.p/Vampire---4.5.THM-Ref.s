%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:31 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   40 (  77 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 188 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f34,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f27,f24,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f56,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f45,f53])).

fof(f53,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0) ),
    inference(unit_resulting_resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f45,plain,(
    ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f25,f42,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f42,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f34,f40,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f40,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f24,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f25,plain,(
    ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : run_vampire %s %d
% 0.09/0.29  % Computer   : n013.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 10:57:54 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.15/0.35  % (16384)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.15/0.36  % (16387)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.15/0.36  % (16382)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.15/0.36  % (16382)Refutation found. Thanks to Tanya!
% 0.15/0.36  % SZS status Theorem for theBenchmark
% 0.15/0.36  % SZS output start Proof for theBenchmark
% 0.15/0.36  fof(f58,plain,(
% 0.15/0.36    $false),
% 0.15/0.36    inference(subsumption_resolution,[],[f56,f37])).
% 0.15/0.36  fof(f37,plain,(
% 0.15/0.36    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 0.15/0.36    inference(unit_resulting_resolution,[],[f34,f28])).
% 0.15/0.36  fof(f28,plain,(
% 0.15/0.36    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.15/0.36    inference(cnf_transformation,[],[f15])).
% 0.15/0.36  fof(f15,plain,(
% 0.15/0.36    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.15/0.36    inference(ennf_transformation,[],[f5])).
% 0.15/0.36  fof(f5,axiom,(
% 0.15/0.36    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.15/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.15/0.36  fof(f34,plain,(
% 0.15/0.36    v1_relat_1(sK3)),
% 0.15/0.36    inference(unit_resulting_resolution,[],[f27,f24,f26])).
% 0.15/0.36  fof(f26,plain,(
% 0.15/0.36    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.15/0.36    inference(cnf_transformation,[],[f14])).
% 0.15/0.36  fof(f14,plain,(
% 0.15/0.36    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.15/0.36    inference(ennf_transformation,[],[f2])).
% 0.15/0.36  fof(f2,axiom,(
% 0.15/0.36    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.15/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.15/0.36  fof(f24,plain,(
% 0.15/0.36    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.15/0.36    inference(cnf_transformation,[],[f22])).
% 0.15/0.36  fof(f22,plain,(
% 0.15/0.36    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.15/0.36    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21])).
% 0.15/0.36  fof(f21,plain,(
% 0.15/0.36    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.15/0.36    introduced(choice_axiom,[])).
% 0.15/0.36  fof(f13,plain,(
% 0.15/0.36    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.36    inference(ennf_transformation,[],[f11])).
% 0.15/0.36  fof(f11,plain,(
% 0.15/0.36    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.15/0.36    inference(pure_predicate_removal,[],[f10])).
% 0.15/0.36  fof(f10,plain,(
% 0.15/0.36    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.15/0.36    inference(pure_predicate_removal,[],[f9])).
% 0.15/0.36  fof(f9,negated_conjecture,(
% 0.15/0.36    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.15/0.36    inference(negated_conjecture,[],[f8])).
% 0.15/0.36  fof(f8,conjecture,(
% 0.15/0.36    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.15/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).
% 0.15/0.36  fof(f27,plain,(
% 0.15/0.36    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.15/0.36    inference(cnf_transformation,[],[f4])).
% 0.15/0.36  fof(f4,axiom,(
% 0.15/0.36    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.15/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.15/0.36  fof(f56,plain,(
% 0.15/0.36    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 0.15/0.36    inference(backward_demodulation,[],[f45,f53])).
% 0.15/0.36  fof(f53,plain,(
% 0.15/0.36    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)) )),
% 0.15/0.36    inference(unit_resulting_resolution,[],[f24,f33])).
% 0.15/0.36  fof(f33,plain,(
% 0.15/0.36    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.15/0.36    inference(cnf_transformation,[],[f20])).
% 0.15/0.36  fof(f20,plain,(
% 0.15/0.36    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.36    inference(ennf_transformation,[],[f7])).
% 0.15/0.36  fof(f7,axiom,(
% 0.15/0.36    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.15/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.15/0.36  fof(f45,plain,(
% 0.15/0.36    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),k2_relat_1(sK3))),
% 0.15/0.36    inference(unit_resulting_resolution,[],[f25,f42,f32])).
% 0.15/0.36  fof(f32,plain,(
% 0.15/0.36    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.15/0.36    inference(cnf_transformation,[],[f19])).
% 0.15/0.36  fof(f19,plain,(
% 0.15/0.36    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.15/0.36    inference(flattening,[],[f18])).
% 0.15/0.36  fof(f18,plain,(
% 0.15/0.36    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.15/0.36    inference(ennf_transformation,[],[f1])).
% 0.15/0.36  fof(f1,axiom,(
% 0.15/0.36    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.15/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.15/0.36  fof(f42,plain,(
% 0.15/0.36    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.15/0.36    inference(unit_resulting_resolution,[],[f34,f40,f29])).
% 0.15/0.36  fof(f29,plain,(
% 0.15/0.36    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.15/0.36    inference(cnf_transformation,[],[f23])).
% 0.15/0.36  fof(f23,plain,(
% 0.15/0.36    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.15/0.36    inference(nnf_transformation,[],[f16])).
% 0.15/0.36  fof(f16,plain,(
% 0.15/0.36    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.15/0.36    inference(ennf_transformation,[],[f3])).
% 0.15/0.36  fof(f3,axiom,(
% 0.15/0.36    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.15/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.15/0.36  fof(f40,plain,(
% 0.15/0.36    v5_relat_1(sK3,sK1)),
% 0.15/0.36    inference(unit_resulting_resolution,[],[f24,f31])).
% 0.15/0.36  fof(f31,plain,(
% 0.15/0.36    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.15/0.36    inference(cnf_transformation,[],[f17])).
% 0.15/0.36  fof(f17,plain,(
% 0.15/0.36    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.36    inference(ennf_transformation,[],[f12])).
% 0.15/0.36  fof(f12,plain,(
% 0.15/0.36    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.15/0.36    inference(pure_predicate_removal,[],[f6])).
% 0.15/0.36  fof(f6,axiom,(
% 0.15/0.36    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.15/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.15/0.36  fof(f25,plain,(
% 0.15/0.36    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)),
% 0.15/0.36    inference(cnf_transformation,[],[f22])).
% 0.15/0.36  % SZS output end Proof for theBenchmark
% 0.15/0.36  % (16382)------------------------------
% 0.15/0.36  % (16382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.36  % (16382)Termination reason: Refutation
% 0.15/0.36  
% 0.15/0.36  % (16382)Memory used [KB]: 6140
% 0.15/0.36  % (16382)Time elapsed: 0.004 s
% 0.15/0.36  % (16382)------------------------------
% 0.15/0.36  % (16382)------------------------------
% 0.15/0.36  % (16379)Success in time 0.06 s
%------------------------------------------------------------------------------
