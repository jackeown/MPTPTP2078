%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 197 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  173 ( 310 expanded)
%              Number of equality atoms :   68 ( 157 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f737,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f736])).

fof(f736,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f460,f735])).

fof(f735,plain,(
    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(resolution,[],[f734,f64])).

fof(f64,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f734,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(resolution,[],[f733,f63])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f38,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f733,plain,
    ( ~ v1_funct_1(k6_partfun1(sK0))
    | sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ v1_relat_1(k6_partfun1(sK0)) ),
    inference(resolution,[],[f731,f65])).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f40,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f731,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f729,f362])).

fof(f362,plain,(
    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) ),
    inference(forward_demodulation,[],[f356,f70])).

fof(f70,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f36])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f356,plain,(
    k2_relat_1(k6_partfun1(sK1)) = k9_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f193,f334])).

fof(f334,plain,(
    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) ),
    inference(resolution,[],[f331,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X1) ) ),
    inference(resolution,[],[f56,f64])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f331,plain,(
    v4_relat_1(k6_partfun1(sK1),sK0) ),
    inference(resolution,[],[f329,f68])).

fof(f68,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f42,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f329,plain,(
    ! [X0] :
      ( ~ v4_relat_1(k6_partfun1(X0),sK1)
      | v4_relat_1(k6_partfun1(X0),sK0) ) ),
    inference(resolution,[],[f82,f75])).

fof(f75,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | v4_relat_1(k6_partfun1(X0),X2)
      | ~ v4_relat_1(k6_partfun1(X0),X1) ) ),
    inference(resolution,[],[f54,f64])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f193,plain,(
    ! [X17,X16] : k9_relat_1(k6_partfun1(X16),X17) = k2_relat_1(k7_relat_1(k6_partfun1(X17),X16)) ),
    inference(superposition,[],[f70,f109])).

fof(f109,plain,(
    ! [X0,X1] : k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X1),X0)) ),
    inference(backward_demodulation,[],[f86,f104])).

fof(f104,plain,(
    ! [X14,X15] : k1_setfam_1(k2_enumset1(X14,X14,X14,X15)) = k9_relat_1(k6_partfun1(X14),X15) ),
    inference(forward_demodulation,[],[f95,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f53,f64])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f95,plain,(
    ! [X14,X15] : k1_setfam_1(k2_enumset1(X14,X14,X14,X15)) = k2_relat_1(k7_relat_1(k6_partfun1(X14),X15)) ),
    inference(superposition,[],[f70,f81])).

fof(f81,plain,(
    ! [X0,X1] : k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(backward_demodulation,[],[f73,f80])).

fof(f80,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f74,f64])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f52,f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f36,f36,f36,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f86,plain,(
    ! [X0,X1] : k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(superposition,[],[f81,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f48,f61,f61])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f729,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0)) ),
    inference(resolution,[],[f261,f75])).

fof(f261,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v2_funct_1(k6_partfun1(X0))
      | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f55,f71])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f36])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f460,plain,(
    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f35,f171])).

fof(f171,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f60,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f35,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:52:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (980)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (979)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (977)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (974)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (988)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (975)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (986)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (986)Refutation not found, incomplete strategy% (986)------------------------------
% 0.22/0.48  % (986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (986)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (986)Memory used [KB]: 10618
% 0.22/0.48  % (986)Time elapsed: 0.071 s
% 0.22/0.48  % (986)------------------------------
% 0.22/0.48  % (986)------------------------------
% 0.22/0.48  % (984)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (981)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (982)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (990)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (992)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (987)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (976)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (989)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (975)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f737,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f736])).
% 0.22/0.50  fof(f736,plain,(
% 0.22/0.50    sK1 != sK1),
% 0.22/0.50    inference(superposition,[],[f460,f735])).
% 0.22/0.50  fof(f735,plain,(
% 0.22/0.50    sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.50    inference(resolution,[],[f734,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f37,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,axiom,(
% 0.22/0.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.50  fof(f734,plain,(
% 0.22/0.50    ~v1_relat_1(k6_partfun1(sK0)) | sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.50    inference(resolution,[],[f733,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f38,f36])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f733,plain,(
% 0.22/0.50    ~v1_funct_1(k6_partfun1(sK0)) | sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | ~v1_relat_1(k6_partfun1(sK0))),
% 0.22/0.50    inference(resolution,[],[f731,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f40,f36])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.50  fof(f731,plain,(
% 0.22/0.50    ~v2_funct_1(k6_partfun1(sK0)) | sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0))),
% 0.22/0.50    inference(forward_demodulation,[],[f729,f362])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    sK1 = k9_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.50    inference(forward_demodulation,[],[f356,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.22/0.50    inference(definition_unfolding,[],[f47,f36])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    k2_relat_1(k6_partfun1(sK1)) = k9_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.50    inference(superposition,[],[f193,f334])).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.50    inference(resolution,[],[f331,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(resolution,[],[f56,f64])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.50  fof(f331,plain,(
% 0.22/0.50    v4_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.50    inference(resolution,[],[f329,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f42,f36])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.22/0.50  fof(f329,plain,(
% 0.22/0.50    ( ! [X0] : (~v4_relat_1(k6_partfun1(X0),sK1) | v4_relat_1(k6_partfun1(X0),sK0)) )),
% 0.22/0.50    inference(resolution,[],[f82,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    r1_tarski(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f57,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.50    inference(negated_conjecture,[],[f19])).
% 0.22/0.50  fof(f19,conjecture,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | v4_relat_1(k6_partfun1(X0),X2) | ~v4_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(resolution,[],[f54,f64])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X17,X16] : (k9_relat_1(k6_partfun1(X16),X17) = k2_relat_1(k7_relat_1(k6_partfun1(X17),X16))) )),
% 0.22/0.50    inference(superposition,[],[f70,f109])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X1),X0))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f86,f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X14,X15] : (k1_setfam_1(k2_enumset1(X14,X14,X14,X15)) = k9_relat_1(k6_partfun1(X14),X15)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f95,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(resolution,[],[f53,f64])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X14,X15] : (k1_setfam_1(k2_enumset1(X14,X14,X14,X15)) = k2_relat_1(k7_relat_1(k6_partfun1(X14),X15))) )),
% 0.22/0.50    inference(superposition,[],[f70,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f73,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(resolution,[],[f74,f64])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f52,f36])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f51,f36,f36,f36,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f50,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f49,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(superposition,[],[f81,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f48,f61,f61])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.50  fof(f729,plain,(
% 0.22/0.50    ~v2_funct_1(k6_partfun1(sK0)) | sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1)) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0))),
% 0.22/0.50    inference(resolution,[],[f261,f75])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v2_funct_1(k6_partfun1(X0)) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.22/0.50    inference(superposition,[],[f55,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.22/0.50    inference(definition_unfolding,[],[f46,f36])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.22/0.50  fof(f460,plain,(
% 0.22/0.50    sK1 != k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.50    inference(superposition,[],[f35,f171])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(resolution,[],[f60,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,axiom,(
% 0.22/0.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (975)------------------------------
% 0.22/0.50  % (975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (975)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (975)Memory used [KB]: 2046
% 0.22/0.50  % (975)Time elapsed: 0.072 s
% 0.22/0.50  % (975)------------------------------
% 0.22/0.50  % (975)------------------------------
% 0.22/0.50  % (971)Success in time 0.138 s
%------------------------------------------------------------------------------
