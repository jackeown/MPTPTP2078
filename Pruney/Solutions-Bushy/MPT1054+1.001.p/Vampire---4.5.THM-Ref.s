%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1054+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 120 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  213 ( 305 expanded)
%              Number of equality atoms :   32 (  56 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f56])).

fof(f56,plain,(
    sK2 != k8_relset_1(sK1,sK1,k6_relat_1(sK1),sK2) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f32,plain,(
    sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f95,plain,(
    sK2 = k8_relset_1(sK1,sK1,k6_relat_1(sK1),sK2) ),
    inference(forward_demodulation,[],[f94,f66])).

fof(f66,plain,(
    sK2 = k9_relat_1(k6_relat_1(sK1),sK2) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f94,plain,(
    sK2 = k8_relset_1(sK1,sK1,k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),sK2)) ),
    inference(forward_demodulation,[],[f93,f71])).

fof(f71,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k7_relset_1(X0,X0,k6_relat_1(X0),X1) ),
    inference(resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f41,f33])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f93,plain,(
    sK2 = k8_relset_1(sK1,sK1,k6_relat_1(sK1),k7_relset_1(sK1,sK1,k6_relat_1(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f92,f39])).

fof(f39,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f92,plain,
    ( sK2 = k8_relset_1(sK1,sK1,k6_relat_1(sK1),k7_relset_1(sK1,sK1,k6_relat_1(sK1),sK2))
    | ~ v1_funct_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f91,f70])).

fof(f70,plain,(
    ! [X0] : v1_funct_2(k6_relat_1(X0),X0,X0) ),
    inference(subsumption_resolution,[],[f69,f39])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | v1_funct_2(k6_relat_1(X0),X0,X0) ) ),
    inference(subsumption_resolution,[],[f68,f58])).

fof(f58,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f40,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_partfun1(k6_relat_1(X0),X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | v1_funct_2(k6_relat_1(X0),X0,X0) ) ),
    inference(resolution,[],[f52,f57])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f91,plain,
    ( sK2 = k8_relset_1(sK1,sK1,k6_relat_1(sK1),k7_relset_1(sK1,sK1,k6_relat_1(sK1),sK2))
    | ~ v1_funct_2(k6_relat_1(sK1),sK1,sK1)
    | ~ v1_funct_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f90,f77])).

fof(f77,plain,(
    ! [X0] : v3_funct_2(k6_relat_1(X0),X0,X0) ),
    inference(resolution,[],[f76,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v3_funct_2(X1,X0,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f76,plain,(
    ! [X0] : sP0(X0,k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f75,f65])).

fof(f65,plain,(
    ! [X0] : v1_relat_2(k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v8_relat_2(k6_relat_1(X0))
      & v4_relat_2(k6_relat_1(X0))
      & v3_relat_2(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_partfun1)).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_2(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0] : v3_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_2(k6_relat_1(X0))
      | ~ v3_relat_2(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0] : v8_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v8_relat_2(X0)
      | v1_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v8_relat_2(X0)
        & v3_relat_2(X0)
        & v1_relat_1(X0) )
     => ( v1_relat_2(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_partfun1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_2(k6_relat_1(X0))
      | sP0(X0,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f74,f39])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_2(k6_relat_1(X0))
      | sP0(X0,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f73,f58])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_partfun1(k6_relat_1(X0),X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_2(k6_relat_1(X0))
      | sP0(X0,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f72,f57])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f48,f52])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(definition_folding,[],[f19,f25])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( ( v1_funct_2(X1,X0,X0)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v1_relat_2(X1) )
       => ( v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_funct_2)).

fof(f90,plain,
    ( sK2 = k8_relset_1(sK1,sK1,k6_relat_1(sK1),k7_relset_1(sK1,sK1,k6_relat_1(sK1),sK2))
    | ~ v3_funct_2(k6_relat_1(sK1),sK1,sK1)
    | ~ v1_funct_2(k6_relat_1(sK1),sK1,sK1)
    | ~ v1_funct_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f88,f57])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      | sK2 = k8_relset_1(sK1,sK1,X0,k7_relset_1(sK1,sK1,X0,sK2))
      | ~ v3_funct_2(X0,sK1,sK1)
      | ~ v1_funct_2(X0,sK1,sK1)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
        & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 )
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
        & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 )
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

%------------------------------------------------------------------------------
