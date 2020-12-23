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
% DateTime   : Thu Dec  3 13:07:12 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 135 expanded)
%              Number of equality atoms :   34 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f57])).

fof(f57,plain,(
    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(resolution,[],[f56,f41])).

fof(f41,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f32,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k10_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(forward_demodulation,[],[f55,f51])).

fof(f51,plain,(
    ! [X2,X1] : k10_relat_1(k6_partfun1(X1),X2) = k9_relat_1(k6_partfun1(X1),k10_relat_1(k6_partfun1(X1),X2)) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X0,X1] : m1_subset_1(k10_relat_1(k6_partfun1(X0),X1),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_partfun1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f45,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f23,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f27,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_partfun1(X0),X1),k1_relat_1(k6_partfun1(X0))) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f30,f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X0),X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X0),X1)) = X1
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f26,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X0),X1)) = X1
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f28,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f74,plain,(
    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f22,f72])).

fof(f72,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f34,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f22,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n014.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 09:49:52 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.38  % (31757)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.17/0.38  % (31757)Refutation found. Thanks to Tanya!
% 0.17/0.38  % SZS status Theorem for theBenchmark
% 0.17/0.38  % SZS output start Proof for theBenchmark
% 0.17/0.38  fof(f75,plain,(
% 0.17/0.38    $false),
% 0.17/0.38    inference(subsumption_resolution,[],[f74,f57])).
% 0.17/0.38  fof(f57,plain,(
% 0.17/0.38    sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.17/0.38    inference(resolution,[],[f56,f41])).
% 0.17/0.38  fof(f41,plain,(
% 0.17/0.38    r1_tarski(sK1,sK0)),
% 0.17/0.38    inference(resolution,[],[f32,f21])).
% 0.17/0.38  fof(f21,plain,(
% 0.17/0.38    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.17/0.38    inference(cnf_transformation,[],[f19])).
% 0.17/0.38  fof(f19,plain,(
% 0.17/0.38    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.17/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f18])).
% 0.17/0.38  fof(f18,plain,(
% 0.17/0.38    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.17/0.38    introduced(choice_axiom,[])).
% 0.17/0.38  fof(f12,plain,(
% 0.17/0.38    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.17/0.38    inference(ennf_transformation,[],[f11])).
% 0.17/0.38  fof(f11,negated_conjecture,(
% 0.17/0.38    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.17/0.38    inference(negated_conjecture,[],[f10])).
% 0.17/0.38  fof(f10,conjecture,(
% 0.17/0.38    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.17/0.38  fof(f32,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.17/0.38    inference(cnf_transformation,[],[f20])).
% 0.17/0.38  fof(f20,plain,(
% 0.17/0.38    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.17/0.38    inference(nnf_transformation,[],[f1])).
% 0.17/0.38  fof(f1,axiom,(
% 0.17/0.38    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.17/0.38  fof(f56,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k10_relat_1(k6_partfun1(X0),X1) = X1) )),
% 0.17/0.38    inference(forward_demodulation,[],[f55,f51])).
% 0.17/0.38  fof(f51,plain,(
% 0.17/0.38    ( ! [X2,X1] : (k10_relat_1(k6_partfun1(X1),X2) = k9_relat_1(k6_partfun1(X1),k10_relat_1(k6_partfun1(X1),X2))) )),
% 0.17/0.38    inference(resolution,[],[f40,f47])).
% 0.17/0.38  fof(f47,plain,(
% 0.17/0.38    ( ! [X0,X1] : (m1_subset_1(k10_relat_1(k6_partfun1(X0),X1),k1_zfmisc_1(X0))) )),
% 0.17/0.38    inference(resolution,[],[f46,f33])).
% 0.17/0.38  fof(f33,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.17/0.38    inference(cnf_transformation,[],[f20])).
% 0.17/0.38  fof(f46,plain,(
% 0.17/0.38    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_partfun1(X0),X1),X0)) )),
% 0.17/0.38    inference(forward_demodulation,[],[f45,f39])).
% 0.17/0.38  fof(f39,plain,(
% 0.17/0.38    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.17/0.38    inference(definition_unfolding,[],[f27,f23])).
% 0.17/0.38  fof(f23,plain,(
% 0.17/0.38    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.17/0.38    inference(cnf_transformation,[],[f9])).
% 0.17/0.38  fof(f9,axiom,(
% 0.17/0.38    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.17/0.38  fof(f27,plain,(
% 0.17/0.38    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.17/0.38    inference(cnf_transformation,[],[f3])).
% 0.17/0.38  fof(f3,axiom,(
% 0.17/0.38    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.17/0.38  fof(f45,plain,(
% 0.17/0.38    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_partfun1(X0),X1),k1_relat_1(k6_partfun1(X0)))) )),
% 0.17/0.38    inference(resolution,[],[f29,f37])).
% 0.17/0.38  fof(f37,plain,(
% 0.17/0.38    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.17/0.38    inference(definition_unfolding,[],[f25,f23])).
% 0.17/0.38  fof(f25,plain,(
% 0.17/0.38    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.17/0.38    inference(cnf_transformation,[],[f4])).
% 0.17/0.38  fof(f4,axiom,(
% 0.17/0.38    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.17/0.38  fof(f29,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.17/0.38    inference(cnf_transformation,[],[f13])).
% 0.17/0.38  fof(f13,plain,(
% 0.17/0.38    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.17/0.38    inference(ennf_transformation,[],[f2])).
% 0.17/0.38  fof(f2,axiom,(
% 0.17/0.38    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.17/0.38  fof(f40,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = X1) )),
% 0.17/0.38    inference(definition_unfolding,[],[f30,f23])).
% 0.17/0.38  fof(f30,plain,(
% 0.17/0.38    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.17/0.38    inference(cnf_transformation,[],[f14])).
% 0.17/0.38  fof(f14,plain,(
% 0.17/0.38    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.17/0.38    inference(ennf_transformation,[],[f6])).
% 0.17/0.38  fof(f6,axiom,(
% 0.17/0.38    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.17/0.38  fof(f55,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X0),X1)) = X1) )),
% 0.17/0.38    inference(subsumption_resolution,[],[f54,f37])).
% 0.17/0.38  fof(f54,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X0),X1)) = X1 | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.17/0.38    inference(subsumption_resolution,[],[f53,f36])).
% 0.17/0.38  fof(f36,plain,(
% 0.17/0.38    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.17/0.38    inference(definition_unfolding,[],[f26,f23])).
% 0.17/0.38  fof(f26,plain,(
% 0.17/0.38    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.17/0.38    inference(cnf_transformation,[],[f4])).
% 0.17/0.38  fof(f53,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X0),X1)) = X1 | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.17/0.38    inference(superposition,[],[f31,f38])).
% 0.17/0.38  fof(f38,plain,(
% 0.17/0.38    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.17/0.38    inference(definition_unfolding,[],[f28,f23])).
% 0.17/0.38  fof(f28,plain,(
% 0.17/0.38    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.17/0.38    inference(cnf_transformation,[],[f3])).
% 0.17/0.38  fof(f31,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.38    inference(cnf_transformation,[],[f16])).
% 0.17/0.38  fof(f16,plain,(
% 0.17/0.38    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.17/0.38    inference(flattening,[],[f15])).
% 0.17/0.38  fof(f15,plain,(
% 0.17/0.38    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.17/0.38    inference(ennf_transformation,[],[f5])).
% 0.17/0.38  fof(f5,axiom,(
% 0.17/0.38    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.17/0.38  fof(f74,plain,(
% 0.17/0.38    sK1 != k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.17/0.38    inference(superposition,[],[f22,f72])).
% 0.17/0.38  fof(f72,plain,(
% 0.17/0.38    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.17/0.38    inference(resolution,[],[f34,f35])).
% 0.17/0.38  fof(f35,plain,(
% 0.17/0.38    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.17/0.38    inference(definition_unfolding,[],[f24,f23])).
% 0.17/0.38  fof(f24,plain,(
% 0.17/0.38    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.17/0.38    inference(cnf_transformation,[],[f8])).
% 0.17/0.38  fof(f8,axiom,(
% 0.17/0.38    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.17/0.38  fof(f34,plain,(
% 0.17/0.38    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.17/0.38    inference(cnf_transformation,[],[f17])).
% 0.17/0.38  fof(f17,plain,(
% 0.17/0.38    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.38    inference(ennf_transformation,[],[f7])).
% 0.17/0.38  fof(f7,axiom,(
% 0.17/0.38    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.17/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.17/0.38  fof(f22,plain,(
% 0.17/0.38    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.17/0.38    inference(cnf_transformation,[],[f19])).
% 0.17/0.38  % SZS output end Proof for theBenchmark
% 0.17/0.38  % (31757)------------------------------
% 0.17/0.38  % (31757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.38  % (31757)Termination reason: Refutation
% 0.17/0.38  
% 0.17/0.38  % (31757)Memory used [KB]: 1663
% 0.17/0.38  % (31757)Time elapsed: 0.005 s
% 0.17/0.38  % (31757)------------------------------
% 0.17/0.38  % (31757)------------------------------
% 0.17/0.39  % (31743)Success in time 0.063 s
%------------------------------------------------------------------------------
