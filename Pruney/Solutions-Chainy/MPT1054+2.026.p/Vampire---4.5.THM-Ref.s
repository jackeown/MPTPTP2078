%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 221 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  153 ( 365 expanded)
%              Number of equality atoms :   63 ( 160 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f98,f107])).

fof(f107,plain,(
    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f105,f74])).

fof(f74,plain,(
    ! [X0] : k9_relat_1(k6_partfun1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f73,f64])).

fof(f64,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f38])).

fof(f38,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f73,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = k9_relat_1(k6_partfun1(X0),X0) ),
    inference(superposition,[],[f69,f72])).

fof(f72,plain,(
    ! [X0] : k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X0) ),
    inference(resolution,[],[f70,f62])).

fof(f62,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f45,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X1) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f69,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f49,f59])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f105,plain,(
    ! [X0] : k9_relat_1(k6_partfun1(sK1),X0) = k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0)) ),
    inference(forward_demodulation,[],[f103,f96])).

fof(f96,plain,(
    ! [X0,X1] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f95,f59])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_partfun1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ) ),
    inference(resolution,[],[f91,f60])).

fof(f60,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f43,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f90,f57])).

fof(f57,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f39,f38,f38])).

fof(f39,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k2_funct_1(k6_partfun1(X0)),X1)
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f53,f58])).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f41,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f103,plain,(
    ! [X0] : k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0)) = k10_relat_1(k6_partfun1(sK1),X0) ),
    inference(superposition,[],[f102,f88])).

fof(f88,plain,(
    k6_partfun1(sK1) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK1)) ),
    inference(resolution,[],[f87,f67])).

fof(f67,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f34])).

fof(f34,plain,
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_partfun1(X0) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f86,f65])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f38])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_partfun1(X0)),X1)
      | k6_partfun1(X0) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ) ),
    inference(resolution,[],[f66,f59])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f50,f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f102,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k9_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X1),X2)) ),
    inference(forward_demodulation,[],[f101,f96])).

fof(f101,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X1),X2)) ),
    inference(resolution,[],[f100,f59])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(k6_partfun1(X1),X0),X2) = k9_relat_1(k6_partfun1(X1),k10_relat_1(X0,X2)) ) ),
    inference(forward_demodulation,[],[f92,f96])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(k6_partfun1(X1),X0),X2) = k10_relat_1(k6_partfun1(X1),k10_relat_1(X0,X2)) ) ),
    inference(resolution,[],[f51,f59])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f98,plain,(
    sK1 != k9_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f94,f96])).

fof(f94,plain,(
    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) ),
    inference(superposition,[],[f37,f93])).

fof(f93,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f37,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:48:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (1730)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (1730)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (1736)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (1728)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (1742)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (1738)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (1734)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (1735)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    sK1 != sK1),
% 0.21/0.48    inference(superposition,[],[f98,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    sK1 = k9_relat_1(k6_partfun1(sK0),sK1)),
% 0.21/0.48    inference(superposition,[],[f105,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(k6_partfun1(X0),X0) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f73,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f48,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = k9_relat_1(k6_partfun1(X0),X0)) )),
% 0.21/0.48    inference(superposition,[],[f69,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0] : (k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X0)) )),
% 0.21/0.48    inference(resolution,[],[f70,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f45,f38])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | k6_partfun1(X0) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(resolution,[],[f54,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f40,f38])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(resolution,[],[f49,f59])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(k6_partfun1(sK1),X0) = k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f103,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(resolution,[],[f95,f59])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(k6_partfun1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(resolution,[],[f91,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f43,f38])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(k6_partfun1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f90,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f38,f38])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k2_funct_1(k6_partfun1(X0)),X1) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f53,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f41,f38])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK1),X0)) = k10_relat_1(k6_partfun1(sK1),X0)) )),
% 0.21/0.48    inference(superposition,[],[f102,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    k6_partfun1(sK1) = k5_relat_1(k6_partfun1(sK0),k6_partfun1(sK1))),
% 0.21/0.48    inference(resolution,[],[f87,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0)),
% 0.21/0.48    inference(resolution,[],[f55,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.48    inference(negated_conjecture,[],[f16])).
% 0.21/0.48  fof(f16,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_partfun1(X0) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f86,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f47,f38])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_partfun1(X0)),X1) | k6_partfun1(X0) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f66,f59])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_partfun1(X0),X1) = X1) )),
% 0.21/0.48    inference(definition_unfolding,[],[f50,f38])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k9_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X1),X2))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f101,f96])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)),X2) = k9_relat_1(k6_partfun1(X0),k10_relat_1(k6_partfun1(X1),X2))) )),
% 0.21/0.48    inference(resolution,[],[f100,f59])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(k6_partfun1(X1),X0),X2) = k9_relat_1(k6_partfun1(X1),k10_relat_1(X0,X2))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f92,f96])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(k6_partfun1(X1),X0),X2) = k10_relat_1(k6_partfun1(X1),k10_relat_1(X0,X2))) )),
% 0.21/0.48    inference(resolution,[],[f51,f59])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    sK1 != k9_relat_1(k6_partfun1(sK0),sK1)),
% 0.21/0.48    inference(superposition,[],[f94,f96])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    sK1 != k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.21/0.48    inference(superposition,[],[f37,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(resolution,[],[f56,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (1730)------------------------------
% 0.21/0.48  % (1730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1730)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (1730)Memory used [KB]: 6140
% 0.21/0.48  % (1730)Time elapsed: 0.055 s
% 0.21/0.48  % (1730)------------------------------
% 0.21/0.48  % (1730)------------------------------
% 0.21/0.48  % (1727)Success in time 0.126 s
%------------------------------------------------------------------------------
