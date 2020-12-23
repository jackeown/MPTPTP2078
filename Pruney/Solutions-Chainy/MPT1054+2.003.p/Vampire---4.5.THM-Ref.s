%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:06 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 230 expanded)
%              Number of leaves         :   21 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  182 ( 352 expanded)
%              Number of equality atoms :   69 ( 168 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1796,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1795,f974])).

fof(f974,plain,(
    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f37,f970])).

fof(f970,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f64,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f37,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f1795,plain,(
    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(forward_demodulation,[],[f1786,f258])).

fof(f258,plain,(
    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) ),
    inference(forward_demodulation,[],[f247,f74])).

fof(f74,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f39])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f247,plain,(
    k2_relat_1(k6_partfun1(sK1)) = k9_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f89,f211])).

fof(f211,plain,(
    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f129,f105])).

fof(f105,plain,(
    sK1 = k9_relat_1(k6_partfun1(sK1),sK0) ),
    inference(forward_demodulation,[],[f104,f74])).

fof(f104,plain,(
    k9_relat_1(k6_partfun1(sK1),sK0) = k2_relat_1(k6_partfun1(sK1)) ),
    inference(superposition,[],[f89,f102])).

fof(f102,plain,(
    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) ),
    inference(resolution,[],[f99,f85])).

fof(f85,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f83,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f83,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f38,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f81,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f56,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f99,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_partfun1(X3) = k7_relat_1(k6_partfun1(X3),X4) ) ),
    inference(resolution,[],[f97,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X1) ) ),
    inference(resolution,[],[f58,f69])).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k6_partfun1(X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f93,f72])).

fof(f72,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f46,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X2),X0)
      | ~ r1_tarski(X0,X1)
      | v4_relat_1(k6_partfun1(X2),X1) ) ),
    inference(resolution,[],[f55,f69])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1) ) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f129,plain,(
    ! [X0,X1] : k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X1),X0)) ),
    inference(backward_demodulation,[],[f106,f126])).

fof(f126,plain,(
    ! [X10,X11] : k1_setfam_1(k2_enumset1(X10,X10,X10,X11)) = k9_relat_1(k6_partfun1(X10),X11) ),
    inference(forward_demodulation,[],[f113,f89])).

fof(f113,plain,(
    ! [X10,X11] : k1_setfam_1(k2_enumset1(X10,X10,X10,X11)) = k2_relat_1(k7_relat_1(k6_partfun1(X10),X11)) ),
    inference(superposition,[],[f74,f92])).

fof(f92,plain,(
    ! [X0,X1] : k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(backward_demodulation,[],[f77,f91])).

fof(f91,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f78,f69])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f53,f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f77,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f39,f39,f39,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f106,plain,(
    ! [X0,X1] : k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(superposition,[],[f92,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f49,f65,f65])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f89,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f54,f69])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1786,plain,(
    sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1)) ),
    inference(resolution,[],[f1768,f85])).

fof(f1768,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f1767,f75])).

fof(f75,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f1767,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))
      | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f1766,f69])).

fof(f1766,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))
      | ~ v1_relat_1(k6_partfun1(X0))
      | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f1760,f70])).

fof(f70,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f44,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f1760,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))
      | ~ v1_relat_1(k6_partfun1(X0))
      | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 ) ),
    inference(resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f42,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (5998)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (6007)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (5999)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (5990)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.13/0.52  % (6007)Refutation not found, incomplete strategy% (6007)------------------------------
% 1.13/0.52  % (6007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.52  % (5991)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.13/0.52  % (6007)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.52  
% 1.13/0.52  % (6007)Memory used [KB]: 10746
% 1.13/0.52  % (6007)Time elapsed: 0.056 s
% 1.13/0.52  % (6007)------------------------------
% 1.13/0.52  % (6007)------------------------------
% 1.13/0.52  % (5989)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.13/0.53  % (6006)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.13/0.53  % (6006)Refutation not found, incomplete strategy% (6006)------------------------------
% 1.13/0.53  % (6006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.53  % (6006)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.53  
% 1.13/0.53  % (6006)Memory used [KB]: 1663
% 1.13/0.53  % (6006)Time elapsed: 0.111 s
% 1.13/0.53  % (6006)------------------------------
% 1.13/0.53  % (6006)------------------------------
% 1.13/0.53  % (5985)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.13/0.53  % (5997)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.13/0.53  % (5985)Refutation not found, incomplete strategy% (5985)------------------------------
% 1.13/0.53  % (5985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.53  % (5985)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.53  
% 1.13/0.53  % (5985)Memory used [KB]: 1663
% 1.13/0.53  % (5985)Time elapsed: 0.114 s
% 1.13/0.53  % (5985)------------------------------
% 1.13/0.53  % (5985)------------------------------
% 1.32/0.54  % (5987)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (6000)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.54  % (5987)Refutation not found, incomplete strategy% (5987)------------------------------
% 1.32/0.54  % (5987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (5987)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (5987)Memory used [KB]: 10746
% 1.32/0.54  % (5987)Time elapsed: 0.114 s
% 1.32/0.54  % (5987)------------------------------
% 1.32/0.54  % (5987)------------------------------
% 1.32/0.54  % (6014)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.54  % (5989)Refutation not found, incomplete strategy% (5989)------------------------------
% 1.32/0.54  % (5989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (5989)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (5989)Memory used [KB]: 6140
% 1.32/0.54  % (5989)Time elapsed: 0.126 s
% 1.32/0.54  % (5989)------------------------------
% 1.32/0.54  % (5989)------------------------------
% 1.32/0.54  % (6010)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.54  % (6008)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.55  % (6010)Refutation not found, incomplete strategy% (6010)------------------------------
% 1.32/0.55  % (6010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6010)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6010)Memory used [KB]: 6268
% 1.32/0.55  % (6010)Time elapsed: 0.129 s
% 1.32/0.55  % (6010)------------------------------
% 1.32/0.55  % (6010)------------------------------
% 1.32/0.55  % (5996)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.55  % (6013)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (6004)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.55  % (5992)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.55  % (6002)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.55  % (6011)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.55  % (6002)Refutation not found, incomplete strategy% (6002)------------------------------
% 1.32/0.55  % (6002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6002)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6002)Memory used [KB]: 10618
% 1.32/0.55  % (6002)Time elapsed: 0.129 s
% 1.32/0.55  % (6002)------------------------------
% 1.32/0.55  % (6002)------------------------------
% 1.32/0.55  % (6011)Refutation not found, incomplete strategy% (6011)------------------------------
% 1.32/0.55  % (6011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6011)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6011)Memory used [KB]: 10746
% 1.32/0.55  % (6011)Time elapsed: 0.130 s
% 1.32/0.55  % (6011)------------------------------
% 1.32/0.55  % (6011)------------------------------
% 1.32/0.55  % (5996)Refutation not found, incomplete strategy% (5996)------------------------------
% 1.32/0.55  % (5996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (5994)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.55  % (6005)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.55  % (6000)Refutation not found, incomplete strategy% (6000)------------------------------
% 1.32/0.55  % (6000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6000)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6000)Memory used [KB]: 6140
% 1.32/0.55  % (6000)Time elapsed: 0.003 s
% 1.32/0.55  % (6000)------------------------------
% 1.32/0.55  % (6000)------------------------------
% 1.32/0.55  % (5996)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (5996)Memory used [KB]: 10618
% 1.32/0.55  % (5996)Time elapsed: 0.132 s
% 1.32/0.55  % (5996)------------------------------
% 1.32/0.55  % (5996)------------------------------
% 1.32/0.55  % (5994)Refutation not found, incomplete strategy% (5994)------------------------------
% 1.32/0.55  % (5994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (5994)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (5994)Memory used [KB]: 10618
% 1.32/0.55  % (5994)Time elapsed: 0.139 s
% 1.32/0.55  % (5994)------------------------------
% 1.32/0.55  % (5994)------------------------------
% 1.32/0.55  % (6005)Refutation not found, incomplete strategy% (6005)------------------------------
% 1.32/0.55  % (6005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6005)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6005)Memory used [KB]: 10746
% 1.32/0.55  % (6005)Time elapsed: 0.142 s
% 1.32/0.55  % (6005)------------------------------
% 1.32/0.55  % (6005)------------------------------
% 1.32/0.57  % (5988)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.58  % (6003)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.58  % (5986)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.59  % (5993)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.59  % (5993)Refutation not found, incomplete strategy% (5993)------------------------------
% 1.32/0.59  % (5993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.59  % (5993)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.59  
% 1.32/0.59  % (5993)Memory used [KB]: 10618
% 1.32/0.59  % (5993)Time elapsed: 0.181 s
% 1.32/0.59  % (5993)------------------------------
% 1.32/0.59  % (5993)------------------------------
% 1.32/0.60  % (6012)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.60  % (6001)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.61  % (5995)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.61  % (5995)Refutation not found, incomplete strategy% (5995)------------------------------
% 1.32/0.61  % (5995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.61  % (5995)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.61  
% 1.32/0.61  % (5995)Memory used [KB]: 10618
% 1.32/0.61  % (5995)Time elapsed: 0.161 s
% 1.32/0.61  % (5995)------------------------------
% 1.32/0.61  % (5995)------------------------------
% 1.32/0.61  % (5991)Refutation found. Thanks to Tanya!
% 1.32/0.61  % SZS status Theorem for theBenchmark
% 1.32/0.61  % SZS output start Proof for theBenchmark
% 1.32/0.61  fof(f1796,plain,(
% 1.32/0.61    $false),
% 1.32/0.61    inference(subsumption_resolution,[],[f1795,f974])).
% 1.32/0.61  fof(f974,plain,(
% 1.32/0.61    sK1 != k10_relat_1(k6_partfun1(sK0),sK1)),
% 1.32/0.61    inference(superposition,[],[f37,f970])).
% 1.32/0.61  fof(f970,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 1.32/0.61    inference(resolution,[],[f64,f67])).
% 1.32/0.61  fof(f67,plain,(
% 1.32/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.32/0.61    inference(definition_unfolding,[],[f40,f39])).
% 1.32/0.61  fof(f39,plain,(
% 1.32/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f20])).
% 1.32/0.61  fof(f20,axiom,(
% 1.32/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.32/0.61  fof(f40,plain,(
% 1.32/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f19])).
% 1.32/0.61  fof(f19,axiom,(
% 1.32/0.61    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.32/0.61  fof(f64,plain,(
% 1.32/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f35])).
% 1.32/0.61  fof(f35,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.61    inference(ennf_transformation,[],[f18])).
% 1.32/0.61  fof(f18,axiom,(
% 1.32/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.32/0.61  fof(f37,plain,(
% 1.32/0.61    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 1.32/0.61    inference(cnf_transformation,[],[f24])).
% 1.32/0.61  fof(f24,plain,(
% 1.32/0.61    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.61    inference(ennf_transformation,[],[f22])).
% 1.32/0.61  fof(f22,negated_conjecture,(
% 1.32/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.32/0.61    inference(negated_conjecture,[],[f21])).
% 1.32/0.61  fof(f21,conjecture,(
% 1.32/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 1.32/0.61  fof(f1795,plain,(
% 1.32/0.61    sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 1.32/0.61    inference(forward_demodulation,[],[f1786,f258])).
% 1.32/0.61  fof(f258,plain,(
% 1.32/0.61    sK1 = k9_relat_1(k6_partfun1(sK0),sK1)),
% 1.32/0.61    inference(forward_demodulation,[],[f247,f74])).
% 1.32/0.61  fof(f74,plain,(
% 1.32/0.61    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.32/0.61    inference(definition_unfolding,[],[f48,f39])).
% 1.32/0.61  fof(f48,plain,(
% 1.32/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.32/0.61    inference(cnf_transformation,[],[f11])).
% 1.32/0.61  fof(f11,axiom,(
% 1.32/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.32/0.61  fof(f247,plain,(
% 1.32/0.61    k2_relat_1(k6_partfun1(sK1)) = k9_relat_1(k6_partfun1(sK0),sK1)),
% 1.32/0.61    inference(superposition,[],[f89,f211])).
% 1.32/0.61  fof(f211,plain,(
% 1.32/0.61    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK0),sK1)),
% 1.32/0.61    inference(superposition,[],[f129,f105])).
% 1.32/0.61  fof(f105,plain,(
% 1.32/0.61    sK1 = k9_relat_1(k6_partfun1(sK1),sK0)),
% 1.32/0.61    inference(forward_demodulation,[],[f104,f74])).
% 1.32/0.61  fof(f104,plain,(
% 1.32/0.61    k9_relat_1(k6_partfun1(sK1),sK0) = k2_relat_1(k6_partfun1(sK1))),
% 1.32/0.61    inference(superposition,[],[f89,f102])).
% 1.32/0.61  fof(f102,plain,(
% 1.32/0.61    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)),
% 1.32/0.61    inference(resolution,[],[f99,f85])).
% 1.32/0.61  fof(f85,plain,(
% 1.32/0.61    r1_tarski(sK1,sK0)),
% 1.32/0.61    inference(resolution,[],[f83,f79])).
% 1.32/0.61  fof(f79,plain,(
% 1.32/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.32/0.61    inference(equality_resolution,[],[f60])).
% 1.32/0.61  fof(f60,plain,(
% 1.32/0.61    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.32/0.61    inference(cnf_transformation,[],[f4])).
% 1.32/0.61  fof(f4,axiom,(
% 1.32/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.32/0.61  fof(f83,plain,(
% 1.32/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.61    inference(subsumption_resolution,[],[f81,f38])).
% 1.32/0.61  fof(f38,plain,(
% 1.32/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f5])).
% 1.32/0.61  fof(f5,axiom,(
% 1.32/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.32/0.61  fof(f81,plain,(
% 1.32/0.61    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.61    inference(resolution,[],[f56,f36])).
% 1.32/0.61  fof(f36,plain,(
% 1.32/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.61    inference(cnf_transformation,[],[f24])).
% 1.32/0.61  fof(f56,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f30])).
% 1.32/0.61  fof(f30,plain,(
% 1.32/0.61    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.32/0.61    inference(flattening,[],[f29])).
% 1.32/0.61  fof(f29,plain,(
% 1.32/0.61    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.32/0.61    inference(ennf_transformation,[],[f7])).
% 1.32/0.61  fof(f7,axiom,(
% 1.32/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.32/0.61  fof(f99,plain,(
% 1.32/0.61    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_partfun1(X3) = k7_relat_1(k6_partfun1(X3),X4)) )),
% 1.32/0.61    inference(resolution,[],[f97,f90])).
% 1.32/0.61  fof(f90,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 1.32/0.61    inference(resolution,[],[f58,f69])).
% 1.32/0.61  fof(f69,plain,(
% 1.32/0.61    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.32/0.61    inference(definition_unfolding,[],[f41,f39])).
% 1.32/0.61  fof(f41,plain,(
% 1.32/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f15])).
% 1.32/0.61  fof(f15,axiom,(
% 1.32/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.32/0.61  fof(f58,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.32/0.61    inference(cnf_transformation,[],[f34])).
% 1.32/0.61  fof(f34,plain,(
% 1.32/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.32/0.61    inference(flattening,[],[f33])).
% 1.32/0.61  fof(f33,plain,(
% 1.32/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.32/0.61    inference(ennf_transformation,[],[f9])).
% 1.32/0.61  fof(f9,axiom,(
% 1.32/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.32/0.61  fof(f97,plain,(
% 1.32/0.61    ( ! [X0,X1] : (v4_relat_1(k6_partfun1(X0),X1) | ~r1_tarski(X0,X1)) )),
% 1.32/0.61    inference(resolution,[],[f93,f72])).
% 1.32/0.61  fof(f72,plain,(
% 1.32/0.61    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 1.32/0.61    inference(definition_unfolding,[],[f46,f39])).
% 1.32/0.61  fof(f46,plain,(
% 1.32/0.61    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f23])).
% 1.32/0.61  fof(f23,plain,(
% 1.32/0.61    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.32/0.61    inference(pure_predicate_removal,[],[f13])).
% 1.32/0.61  fof(f13,axiom,(
% 1.32/0.61    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 1.32/0.61  fof(f93,plain,(
% 1.32/0.61    ( ! [X2,X0,X1] : (~v4_relat_1(k6_partfun1(X2),X0) | ~r1_tarski(X0,X1) | v4_relat_1(k6_partfun1(X2),X1)) )),
% 1.32/0.61    inference(resolution,[],[f55,f69])).
% 1.32/0.61  fof(f55,plain,(
% 1.32/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f28])).
% 1.32/0.61  fof(f28,plain,(
% 1.32/0.61    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 1.32/0.61    inference(flattening,[],[f27])).
% 1.32/0.61  fof(f27,plain,(
% 1.32/0.61    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 1.32/0.61    inference(ennf_transformation,[],[f10])).
% 1.32/0.61  fof(f10,axiom,(
% 1.32/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 1.32/0.61  fof(f129,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X1),X0))) )),
% 1.32/0.61    inference(backward_demodulation,[],[f106,f126])).
% 1.32/0.61  fof(f126,plain,(
% 1.32/0.61    ( ! [X10,X11] : (k1_setfam_1(k2_enumset1(X10,X10,X10,X11)) = k9_relat_1(k6_partfun1(X10),X11)) )),
% 1.32/0.61    inference(forward_demodulation,[],[f113,f89])).
% 1.32/0.61  fof(f113,plain,(
% 1.32/0.61    ( ! [X10,X11] : (k1_setfam_1(k2_enumset1(X10,X10,X10,X11)) = k2_relat_1(k7_relat_1(k6_partfun1(X10),X11))) )),
% 1.32/0.61    inference(superposition,[],[f74,f92])).
% 1.32/0.61  fof(f92,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 1.32/0.61    inference(backward_demodulation,[],[f77,f91])).
% 1.32/0.61  fof(f91,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 1.32/0.61    inference(resolution,[],[f78,f69])).
% 1.32/0.61  fof(f78,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 1.32/0.61    inference(definition_unfolding,[],[f53,f39])).
% 1.32/0.61  fof(f53,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f25])).
% 1.32/0.61  fof(f25,plain,(
% 1.32/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.32/0.61    inference(ennf_transformation,[],[f12])).
% 1.32/0.61  fof(f12,axiom,(
% 1.32/0.61    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.32/0.61  fof(f77,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.32/0.61    inference(definition_unfolding,[],[f52,f39,f39,f39,f66])).
% 1.32/0.61  fof(f66,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.32/0.61    inference(definition_unfolding,[],[f51,f65])).
% 1.32/0.61  fof(f65,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.61    inference(definition_unfolding,[],[f50,f63])).
% 1.32/0.61  fof(f63,plain,(
% 1.32/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f3])).
% 1.32/0.61  fof(f3,axiom,(
% 1.32/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.61  fof(f50,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f2])).
% 1.32/0.61  fof(f2,axiom,(
% 1.32/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.61  fof(f51,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f6])).
% 1.32/0.61  fof(f6,axiom,(
% 1.32/0.61    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.32/0.61  fof(f52,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f17])).
% 1.32/0.61  fof(f17,axiom,(
% 1.32/0.61    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.32/0.61  fof(f106,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 1.32/0.61    inference(superposition,[],[f92,f76])).
% 1.32/0.61  fof(f76,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.32/0.61    inference(definition_unfolding,[],[f49,f65,f65])).
% 1.32/0.61  fof(f49,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f1])).
% 1.32/0.61  fof(f1,axiom,(
% 1.32/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.32/0.61  fof(f89,plain,(
% 1.32/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 1.32/0.61    inference(resolution,[],[f54,f69])).
% 1.32/0.61  fof(f54,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f26])).
% 1.32/0.61  fof(f26,plain,(
% 1.32/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.32/0.61    inference(ennf_transformation,[],[f8])).
% 1.32/0.61  fof(f8,axiom,(
% 1.32/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.32/0.61  fof(f1786,plain,(
% 1.32/0.61    sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1))),
% 1.32/0.61    inference(resolution,[],[f1768,f85])).
% 1.32/0.61  fof(f1768,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1) )),
% 1.32/0.61    inference(forward_demodulation,[],[f1767,f75])).
% 1.32/0.61  fof(f75,plain,(
% 1.32/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.32/0.61    inference(definition_unfolding,[],[f47,f39])).
% 1.32/0.61  fof(f47,plain,(
% 1.32/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.32/0.61    inference(cnf_transformation,[],[f11])).
% 1.32/0.61  fof(f1767,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1) )),
% 1.32/0.61    inference(subsumption_resolution,[],[f1766,f69])).
% 1.32/0.61  fof(f1766,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) | ~v1_relat_1(k6_partfun1(X0)) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1) )),
% 1.32/0.61    inference(subsumption_resolution,[],[f1760,f70])).
% 1.32/0.61  fof(f70,plain,(
% 1.32/0.61    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 1.32/0.61    inference(definition_unfolding,[],[f44,f39])).
% 1.32/0.61  fof(f44,plain,(
% 1.32/0.61    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f14])).
% 1.32/0.61  fof(f14,axiom,(
% 1.32/0.61    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.32/0.61  fof(f1760,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~v1_funct_1(k6_partfun1(X0)) | ~r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) | ~v1_relat_1(k6_partfun1(X0)) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1) )),
% 1.32/0.61    inference(resolution,[],[f57,f68])).
% 1.32/0.61  fof(f68,plain,(
% 1.32/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.32/0.61    inference(definition_unfolding,[],[f42,f39])).
% 1.32/0.61  fof(f42,plain,(
% 1.32/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f15])).
% 1.32/0.61  fof(f57,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0) )),
% 1.32/0.61    inference(cnf_transformation,[],[f32])).
% 1.32/0.61  fof(f32,plain,(
% 1.32/0.61    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.61    inference(flattening,[],[f31])).
% 1.32/0.61  fof(f31,plain,(
% 1.32/0.61    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.61    inference(ennf_transformation,[],[f16])).
% 1.32/0.61  fof(f16,axiom,(
% 1.32/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.32/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.32/0.61  % SZS output end Proof for theBenchmark
% 1.32/0.61  % (5991)------------------------------
% 1.32/0.61  % (5991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.61  % (5991)Termination reason: Refutation
% 1.32/0.61  
% 1.32/0.61  % (5991)Memory used [KB]: 7419
% 1.32/0.61  % (5991)Time elapsed: 0.147 s
% 1.32/0.61  % (5991)------------------------------
% 1.32/0.61  % (5991)------------------------------
% 1.32/0.62  % (6009)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.63  % (5984)Success in time 0.249 s
%------------------------------------------------------------------------------
