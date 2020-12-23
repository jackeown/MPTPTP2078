%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:17 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 776 expanded)
%              Number of leaves         :   28 ( 213 expanded)
%              Depth                    :   20
%              Number of atoms          :  263 (1605 expanded)
%              Number of equality atoms :  144 ( 921 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(subsumption_resolution,[],[f312,f193])).

fof(f193,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f112,f192])).

fof(f192,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f191,f98])).

fof(f98,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f91])).

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f191,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) ),
    inference(forward_demodulation,[],[f185,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f185,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k5_xboole_0(X0,k1_xboole_0)))) ),
    inference(superposition,[],[f100,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f59,f91])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f100,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))))) ),
    inference(definition_unfolding,[],[f70,f91,f92,f92])).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f91])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f112,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f106,f98])).

fof(f106,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f76,f93,f92,f93,f93])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f312,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f292,f149])).

fof(f149,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f148,f124])).

fof(f124,plain,(
    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f123,f56])).

fof(f56,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f123,plain,(
    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f121,f57])).

fof(f57,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f121,plain,(
    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f62,f113])).

fof(f113,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f58,f55])).

fof(f55,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f148,plain,(
    ! [X2] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f147,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ),
    inference(resolution,[],[f99,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f66,f91])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f147,plain,(
    ! [X2] : k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X2))) ),
    inference(forward_demodulation,[],[f145,f57])).

fof(f145,plain,(
    ! [X2] : k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k1_setfam_1(k2_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X2))) ),
    inference(resolution,[],[f101,f113])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f71,f91])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f292,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f154,f286])).

fof(f286,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f158,f285])).

fof(f285,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f284,f137])).

fof(f137,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f94,f136])).

fof(f136,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f79,f95])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f52,f93])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f94,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f54,f93,f93])).

fof(f54,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f284,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f283,f158])).

fof(f283,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f282,f154])).

fof(f282,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f280,f114])).

fof(f114,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f95])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f280,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f278,f179])).

fof(f179,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k10_relat_1(sK2,sK1)) ) ),
    inference(resolution,[],[f175,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f175,plain,(
    ! [X0] :
      ( r1_xboole_0(k10_relat_1(sK2,sK1),X0)
      | r2_hidden(sK0,X0) ) ),
    inference(superposition,[],[f102,f154])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f93])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f278,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f277,f114])).

fof(f277,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) ) ),
    inference(resolution,[],[f103,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f73,f93,f93])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

fof(f158,plain,(
    sK2 = k7_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f128,f154])).

fof(f128,plain,(
    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f127,f114])).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f74,f126])).

fof(f126,plain,(
    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f80,f95])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f154,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f153,f143])).

fof(f143,plain,(
    k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f142,f138])).

fof(f138,plain,(
    ! [X0] : k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f89,f95])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f142,plain,(
    k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(resolution,[],[f82,f95])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f153,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f152,f96])).

fof(f96,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f51,f93])).

fof(f51,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f152,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(subsumption_resolution,[],[f151,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f88,f95])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:52:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (15031)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (15024)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (15047)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (15025)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (15028)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (15038)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (15039)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (15039)Refutation not found, incomplete strategy% (15039)------------------------------
% 0.21/0.53  % (15039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15039)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15039)Memory used [KB]: 6268
% 0.21/0.53  % (15039)Time elapsed: 0.127 s
% 0.21/0.53  % (15039)------------------------------
% 0.21/0.53  % (15039)------------------------------
% 0.21/0.53  % (15041)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (15029)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (15046)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (15036)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (15034)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (15053)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (15034)Refutation not found, incomplete strategy% (15034)------------------------------
% 0.21/0.54  % (15034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15027)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (15026)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (15023)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (15043)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (15051)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15030)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (15027)Refutation not found, incomplete strategy% (15027)------------------------------
% 0.21/0.54  % (15027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15027)Memory used [KB]: 6524
% 0.21/0.54  % (15027)Time elapsed: 0.128 s
% 0.21/0.54  % (15027)------------------------------
% 0.21/0.54  % (15027)------------------------------
% 0.21/0.54  % (15034)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15034)Memory used [KB]: 10746
% 0.21/0.54  % (15034)Time elapsed: 0.122 s
% 0.21/0.54  % (15034)------------------------------
% 0.21/0.54  % (15034)------------------------------
% 0.21/0.55  % (15046)Refutation not found, incomplete strategy% (15046)------------------------------
% 0.21/0.55  % (15046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15046)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15046)Memory used [KB]: 10746
% 0.21/0.55  % (15046)Time elapsed: 0.135 s
% 0.21/0.55  % (15046)------------------------------
% 0.21/0.55  % (15046)------------------------------
% 0.21/0.55  % (15050)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (15032)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (15044)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (15032)Refutation not found, incomplete strategy% (15032)------------------------------
% 0.21/0.55  % (15032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15032)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15032)Memory used [KB]: 10746
% 0.21/0.55  % (15032)Time elapsed: 0.136 s
% 0.21/0.55  % (15032)------------------------------
% 0.21/0.55  % (15032)------------------------------
% 0.21/0.55  % (15045)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (15048)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (15049)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (15042)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (15035)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.56  % (15041)Refutation not found, incomplete strategy% (15041)------------------------------
% 1.44/0.56  % (15041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (15041)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (15041)Memory used [KB]: 10618
% 1.44/0.56  % (15041)Time elapsed: 0.146 s
% 1.44/0.56  % (15029)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % (15041)------------------------------
% 1.44/0.56  % (15041)------------------------------
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f313,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(subsumption_resolution,[],[f312,f193])).
% 1.44/0.56  fof(f193,plain,(
% 1.44/0.56    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 1.44/0.56    inference(backward_demodulation,[],[f112,f192])).
% 1.44/0.56  fof(f192,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.44/0.56    inference(forward_demodulation,[],[f191,f98])).
% 1.44/0.56  fof(f98,plain,(
% 1.44/0.56    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.44/0.56    inference(definition_unfolding,[],[f65,f91])).
% 1.44/0.56  fof(f91,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f67,f90])).
% 1.44/0.56  fof(f90,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f68,f77])).
% 1.44/0.56  fof(f77,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.56  fof(f68,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f9])).
% 1.44/0.56  fof(f9,axiom,(
% 1.44/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.56  fof(f67,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,axiom,(
% 1.44/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.44/0.56  fof(f65,plain,(
% 1.44/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.56    inference(rectify,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.44/0.56  fof(f191,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))) )),
% 1.44/0.56    inference(forward_demodulation,[],[f185,f60])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.44/0.56  fof(f185,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k5_xboole_0(X0,k1_xboole_0))))) )),
% 1.44/0.56    inference(superposition,[],[f100,f97])).
% 1.44/0.56  fof(f97,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f59,f91])).
% 1.44/0.56  fof(f59,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.44/0.56  fof(f100,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f70,f91,f92,f92])).
% 1.44/0.56  fof(f92,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f69,f91])).
% 1.44/0.56  fof(f69,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.56  fof(f70,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.44/0.56  fof(f112,plain,(
% 1.44/0.56    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 1.44/0.56    inference(forward_demodulation,[],[f106,f98])).
% 1.44/0.56  fof(f106,plain,(
% 1.44/0.56    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))))) )),
% 1.44/0.56    inference(equality_resolution,[],[f104])).
% 1.44/0.56  fof(f104,plain,(
% 1.44/0.56    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f76,f93,f92,f93,f93])).
% 1.44/0.56  fof(f93,plain,(
% 1.44/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f61,f90])).
% 1.44/0.56  fof(f61,plain,(
% 1.44/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.56  fof(f76,plain,(
% 1.44/0.56    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f12])).
% 1.44/0.56  fof(f12,axiom,(
% 1.44/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.44/0.56  fof(f312,plain,(
% 1.44/0.56    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.44/0.56    inference(forward_demodulation,[],[f292,f149])).
% 1.44/0.56  fof(f149,plain,(
% 1.44/0.56    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)) )),
% 1.44/0.56    inference(forward_demodulation,[],[f148,f124])).
% 1.44/0.56  fof(f124,plain,(
% 1.44/0.56    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.44/0.56    inference(forward_demodulation,[],[f123,f56])).
% 1.44/0.56  fof(f56,plain,(
% 1.44/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f19,axiom,(
% 1.44/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.44/0.56  fof(f123,plain,(
% 1.44/0.56    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.44/0.56    inference(forward_demodulation,[],[f121,f57])).
% 1.44/0.56  fof(f57,plain,(
% 1.44/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f121,plain,(
% 1.44/0.56    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 1.44/0.56    inference(resolution,[],[f62,f113])).
% 1.44/0.56  fof(f113,plain,(
% 1.44/0.56    v1_relat_1(k1_xboole_0)),
% 1.44/0.56    inference(superposition,[],[f58,f55])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,axiom,(
% 1.44/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,axiom,(
% 1.44/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.44/0.56  fof(f62,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f34])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.44/0.56  fof(f148,plain,(
% 1.44/0.56    ( ! [X2] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X2)) )),
% 1.44/0.56    inference(forward_demodulation,[],[f147,f115])).
% 1.44/0.56  fof(f115,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) )),
% 1.44/0.56    inference(resolution,[],[f99,f64])).
% 1.44/0.56  fof(f64,plain,(
% 1.44/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f36])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.44/0.56    inference(ennf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.44/0.56  fof(f99,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f66,f91])).
% 1.44/0.56  fof(f66,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.44/0.56  fof(f147,plain,(
% 1.44/0.56    ( ! [X2] : (k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)))) )),
% 1.44/0.56    inference(forward_demodulation,[],[f145,f57])).
% 1.44/0.56  fof(f145,plain,(
% 1.44/0.56    ( ! [X2] : (k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k1_setfam_1(k2_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X2)))) )),
% 1.44/0.56    inference(resolution,[],[f101,f113])).
% 1.44/0.56  fof(f101,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f71,f91])).
% 1.44/0.56  fof(f71,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,axiom,(
% 1.44/0.56    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.44/0.56  fof(f292,plain,(
% 1.44/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(k1_xboole_0,sK1)),
% 1.44/0.56    inference(backward_demodulation,[],[f154,f286])).
% 1.44/0.56  fof(f286,plain,(
% 1.44/0.56    k1_xboole_0 = sK2),
% 1.44/0.56    inference(backward_demodulation,[],[f158,f285])).
% 1.44/0.56  fof(f285,plain,(
% 1.44/0.56    k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.44/0.56    inference(subsumption_resolution,[],[f284,f137])).
% 1.44/0.56  fof(f137,plain,(
% 1.44/0.56    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 1.44/0.56    inference(backward_demodulation,[],[f94,f136])).
% 1.44/0.56  fof(f136,plain,(
% 1.44/0.56    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.44/0.56    inference(resolution,[],[f79,f95])).
% 1.44/0.56  fof(f95,plain,(
% 1.44/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.44/0.56    inference(definition_unfolding,[],[f52,f93])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.44/0.56    inference(cnf_transformation,[],[f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.44/0.56    inference(flattening,[],[f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.44/0.56    inference(ennf_transformation,[],[f29])).
% 1.44/0.56  fof(f29,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.44/0.56    inference(negated_conjecture,[],[f28])).
% 1.44/0.56  fof(f28,conjecture,(
% 1.44/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 1.44/0.56  fof(f79,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f44])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f24])).
% 1.44/0.56  fof(f24,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.44/0.56  fof(f94,plain,(
% 1.44/0.56    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.44/0.56    inference(definition_unfolding,[],[f54,f93,f93])).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.44/0.56    inference(cnf_transformation,[],[f33])).
% 1.44/0.56  fof(f284,plain,(
% 1.44/0.56    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.44/0.56    inference(forward_demodulation,[],[f283,f158])).
% 1.44/0.56  fof(f283,plain,(
% 1.44/0.56    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k10_relat_1(sK2,sK1))) | k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.44/0.56    inference(forward_demodulation,[],[f282,f154])).
% 1.44/0.56  fof(f282,plain,(
% 1.44/0.56    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) | k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.44/0.56    inference(subsumption_resolution,[],[f280,f114])).
% 1.44/0.56  fof(f114,plain,(
% 1.44/0.56    v1_relat_1(sK2)),
% 1.44/0.56    inference(resolution,[],[f78,f95])).
% 1.44/0.56  fof(f78,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f43])).
% 1.44/0.56  fof(f43,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f22])).
% 1.44/0.56  fof(f22,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.44/0.56  fof(f280,plain,(
% 1.44/0.56    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) | ~v1_relat_1(sK2) | k1_xboole_0 = k7_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.44/0.56    inference(resolution,[],[f278,f179])).
% 1.44/0.56  fof(f179,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(sK0,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k10_relat_1(sK2,sK1))) )),
% 1.44/0.56    inference(resolution,[],[f175,f63])).
% 1.44/0.56  fof(f63,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f35])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 1.44/0.56  fof(f175,plain,(
% 1.44/0.56    ( ! [X0] : (r1_xboole_0(k10_relat_1(sK2,sK1),X0) | r2_hidden(sK0,X0)) )),
% 1.44/0.56    inference(superposition,[],[f102,f154])).
% 1.44/0.56  fof(f102,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f72,f93])).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f38])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,axiom,(
% 1.44/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.44/0.56  fof(f278,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f277,f114])).
% 1.44/0.56  fof(f277,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) )),
% 1.44/0.56    inference(resolution,[],[f103,f50])).
% 1.44/0.56  fof(f50,plain,(
% 1.44/0.56    v1_funct_1(sK2)),
% 1.44/0.56    inference(cnf_transformation,[],[f33])).
% 1.44/0.56  fof(f103,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f73,f93,f93])).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(flattening,[],[f39])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ! [X0,X1] : ((k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.44/0.56    inference(ennf_transformation,[],[f21])).
% 1.44/0.56  fof(f21,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).
% 1.44/0.56  fof(f158,plain,(
% 1.44/0.56    sK2 = k7_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.44/0.56    inference(backward_demodulation,[],[f128,f154])).
% 1.44/0.56  fof(f128,plain,(
% 1.44/0.56    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.44/0.56    inference(subsumption_resolution,[],[f127,f114])).
% 1.44/0.56  fof(f127,plain,(
% 1.44/0.56    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.44/0.56    inference(resolution,[],[f74,f126])).
% 1.44/0.56  fof(f126,plain,(
% 1.44/0.56    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.44/0.56    inference(resolution,[],[f80,f95])).
% 1.44/0.56  fof(f80,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.44/0.56    inference(pure_predicate_removal,[],[f23])).
% 1.44/0.56  fof(f23,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.44/0.56  fof(f74,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f42])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(flattening,[],[f41])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.44/0.56    inference(ennf_transformation,[],[f18])).
% 1.44/0.56  fof(f18,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.44/0.56  fof(f154,plain,(
% 1.44/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1)),
% 1.44/0.56    inference(forward_demodulation,[],[f153,f143])).
% 1.44/0.56  fof(f143,plain,(
% 1.44/0.56    k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k10_relat_1(sK2,sK1)),
% 1.44/0.56    inference(forward_demodulation,[],[f142,f138])).
% 1.44/0.56  fof(f138,plain,(
% 1.44/0.56    ( ! [X0] : (k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 1.44/0.56    inference(resolution,[],[f89,f95])).
% 1.44/0.56  fof(f89,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f49])).
% 1.44/0.56  fof(f49,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f25])).
% 1.44/0.56  fof(f25,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.44/0.56  fof(f142,plain,(
% 1.44/0.56    k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.44/0.56    inference(resolution,[],[f82,f95])).
% 1.44/0.56  fof(f82,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f26])).
% 1.44/0.56  fof(f26,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 1.44/0.56  fof(f153,plain,(
% 1.44/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.44/0.56    inference(subsumption_resolution,[],[f152,f96])).
% 1.44/0.56  fof(f96,plain,(
% 1.44/0.56    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.44/0.56    inference(definition_unfolding,[],[f51,f93])).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f33])).
% 1.44/0.56  fof(f152,plain,(
% 1.44/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.44/0.56    inference(subsumption_resolution,[],[f151,f53])).
% 1.44/0.56  fof(f53,plain,(
% 1.44/0.56    k1_xboole_0 != sK1),
% 1.44/0.56    inference(cnf_transformation,[],[f33])).
% 1.44/0.56  fof(f151,plain,(
% 1.44/0.56    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.44/0.56    inference(resolution,[],[f88,f95])).
% 1.44/0.56  fof(f88,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f48])).
% 1.44/0.56  fof(f48,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(flattening,[],[f47])).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f27])).
% 1.44/0.56  fof(f27,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (15029)------------------------------
% 1.44/0.56  % (15029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (15029)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (15029)Memory used [KB]: 6396
% 1.44/0.56  % (15029)Time elapsed: 0.093 s
% 1.44/0.56  % (15029)------------------------------
% 1.44/0.56  % (15029)------------------------------
% 1.44/0.56  % (15040)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.56  % (15052)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.56  % (15022)Success in time 0.197 s
%------------------------------------------------------------------------------
