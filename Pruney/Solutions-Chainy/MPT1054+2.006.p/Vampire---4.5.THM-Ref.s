%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 211 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  171 ( 309 expanded)
%              Number of equality atoms :   73 ( 168 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f654,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f653])).

fof(f653,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f651,f92])).

fof(f92,plain,(
    sK1 = k9_relat_1(k6_partfun1(sK1),sK0) ),
    inference(forward_demodulation,[],[f91,f72])).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f39])).

fof(f39,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f91,plain,(
    k9_relat_1(k6_partfun1(sK1),sK0) = k2_relat_1(k6_partfun1(sK1)) ),
    inference(superposition,[],[f78,f89])).

fof(f89,plain,(
    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) ),
    inference(resolution,[],[f86,f76])).

fof(f76,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f86,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_partfun1(X3) = k7_relat_1(k6_partfun1(X3),X4) ) ),
    inference(resolution,[],[f84,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X1) ) ),
    inference(resolution,[],[f58,f67])).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k6_partfun1(X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f80,f70])).

fof(f70,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | v4_relat_1(k6_partfun1(X0),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f56,f67])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f78,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f55,f67])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f651,plain,(
    sK1 != k9_relat_1(k6_partfun1(sK1),sK0) ),
    inference(superposition,[],[f623,f641])).

fof(f641,plain,(
    ! [X2,X3] : k10_relat_1(k6_partfun1(X3),X2) = k9_relat_1(k6_partfun1(X2),X3) ),
    inference(backward_demodulation,[],[f525,f629])).

fof(f629,plain,(
    ! [X0,X1] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f624,f67])).

fof(f624,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_partfun1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ) ),
    inference(resolution,[],[f178,f66])).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f43,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k6_partfun1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f174,f64])).

fof(f64,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f40,f39,f39])).

fof(f40,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k6_partfun1(X0))
      | k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f525,plain,(
    ! [X2,X3] : k10_relat_1(k6_partfun1(X2),X3) = k10_relat_1(k6_partfun1(X3),X2) ),
    inference(superposition,[],[f481,f73])).

fof(f73,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f39])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f481,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k6_partfun1(k10_relat_1(k6_partfun1(X1),X0))) ),
    inference(backward_demodulation,[],[f262,f449])).

fof(f449,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k10_relat_1(k6_partfun1(X0),X1)) ),
    inference(backward_demodulation,[],[f75,f379])).

fof(f379,plain,(
    ! [X17,X16] : k1_setfam_1(k2_enumset1(X16,X16,X16,X17)) = k10_relat_1(k6_partfun1(X16),X17) ),
    inference(forward_demodulation,[],[f276,f262])).

fof(f276,plain,(
    ! [X17,X16] : k1_setfam_1(k2_enumset1(X16,X16,X16,X17)) = k1_relat_1(k5_relat_1(k6_partfun1(X16),k6_partfun1(X17))) ),
    inference(superposition,[],[f73,f96])).

fof(f96,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f75,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f51,f62,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f75,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f39,f39,f39,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f262,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
    inference(forward_demodulation,[],[f253,f73])).

fof(f253,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) ),
    inference(resolution,[],[f95,f67])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k6_partfun1(X1),X0)) = k10_relat_1(k6_partfun1(X1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f50,f67])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f623,plain,(
    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f38,f620])).

fof(f620,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f61,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f38,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (9343)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.41  % (9343)Refutation not found, incomplete strategy% (9343)------------------------------
% 0.21/0.41  % (9343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (9343)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.41  
% 0.21/0.41  % (9343)Memory used [KB]: 10618
% 0.21/0.41  % (9343)Time elapsed: 0.003 s
% 0.21/0.41  % (9343)------------------------------
% 0.21/0.41  % (9343)------------------------------
% 0.21/0.44  % (9334)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (9334)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f654,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f653])).
% 0.21/0.46  fof(f653,plain,(
% 0.21/0.46    sK1 != sK1),
% 0.21/0.46    inference(superposition,[],[f651,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    sK1 = k9_relat_1(k6_partfun1(sK1),sK0)),
% 0.21/0.46    inference(forward_demodulation,[],[f91,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f49,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,axiom,(
% 0.21/0.46    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    k9_relat_1(k6_partfun1(sK1),sK0) = k2_relat_1(k6_partfun1(sK1))),
% 0.21/0.46    inference(superposition,[],[f78,f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)),
% 0.21/0.46    inference(resolution,[],[f86,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    r1_tarski(sK1,sK0)),
% 0.21/0.46    inference(resolution,[],[f59,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.46    inference(negated_conjecture,[],[f20])).
% 0.21/0.46  fof(f20,conjecture,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.46    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_partfun1(X3) = k7_relat_1(k6_partfun1(X3),X4)) )),
% 0.21/0.46    inference(resolution,[],[f84,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.46    inference(resolution,[],[f58,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f42,f39])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v4_relat_1(k6_partfun1(X0),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(resolution,[],[f80,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f47,f39])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | v4_relat_1(k6_partfun1(X0),X2) | ~r1_tarski(X1,X2)) )),
% 0.21/0.46    inference(resolution,[],[f56,f67])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.46    inference(resolution,[],[f55,f67])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.46  fof(f651,plain,(
% 0.21/0.46    sK1 != k9_relat_1(k6_partfun1(sK1),sK0)),
% 0.21/0.46    inference(superposition,[],[f623,f641])).
% 0.21/0.46  fof(f641,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k10_relat_1(k6_partfun1(X3),X2) = k9_relat_1(k6_partfun1(X2),X3)) )),
% 0.21/0.46    inference(backward_demodulation,[],[f525,f629])).
% 0.21/0.46  fof(f629,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.46    inference(resolution,[],[f624,f67])).
% 0.21/0.46  fof(f624,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(k6_partfun1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.46    inference(resolution,[],[f178,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f43,f39])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_funct_1(k6_partfun1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f174,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f40,f39,f39])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,axiom,(
% 0.21/0.46    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_funct_1(k6_partfun1(X0)) | k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(resolution,[],[f57,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f45,f39])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.21/0.46  fof(f525,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k10_relat_1(k6_partfun1(X2),X3) = k10_relat_1(k6_partfun1(X3),X2)) )),
% 0.21/0.46    inference(superposition,[],[f481,f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f48,f39])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f481,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k6_partfun1(k10_relat_1(k6_partfun1(X1),X0)))) )),
% 0.21/0.46    inference(backward_demodulation,[],[f262,f449])).
% 0.21/0.46  fof(f449,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k10_relat_1(k6_partfun1(X0),X1))) )),
% 0.21/0.46    inference(backward_demodulation,[],[f75,f379])).
% 0.21/0.46  fof(f379,plain,(
% 0.21/0.46    ( ! [X17,X16] : (k1_setfam_1(k2_enumset1(X16,X16,X16,X17)) = k10_relat_1(k6_partfun1(X16),X17)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f276,f262])).
% 0.21/0.46  fof(f276,plain,(
% 0.21/0.46    ( ! [X17,X16] : (k1_setfam_1(k2_enumset1(X16,X16,X16,X17)) = k1_relat_1(k5_relat_1(k6_partfun1(X16),k6_partfun1(X17)))) )),
% 0.21/0.46    inference(superposition,[],[f73,f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 0.21/0.46    inference(superposition,[],[f75,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f51,f62,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f52,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f54,f39,f39,f39,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f53,f62])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,axiom,(
% 0.21/0.46    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f253,f73])).
% 0.21/0.46  fof(f253,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1)))) )),
% 0.21/0.46    inference(resolution,[],[f95,f67])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k6_partfun1(X1),X0)) = k10_relat_1(k6_partfun1(X1),k1_relat_1(X0))) )),
% 0.21/0.46    inference(resolution,[],[f50,f67])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.46  fof(f623,plain,(
% 0.21/0.46    sK1 != k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.21/0.46    inference(superposition,[],[f38,f620])).
% 0.21/0.46  fof(f620,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.46    inference(resolution,[],[f61,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f41,f39])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,axiom,(
% 0.21/0.46    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (9334)------------------------------
% 0.21/0.46  % (9334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (9334)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (9334)Memory used [KB]: 6524
% 0.21/0.46  % (9334)Time elapsed: 0.018 s
% 0.21/0.46  % (9334)------------------------------
% 0.21/0.46  % (9334)------------------------------
% 0.21/0.46  % (9331)Success in time 0.101 s
%------------------------------------------------------------------------------
