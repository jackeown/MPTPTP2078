%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:21 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 200 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 519 expanded)
%              Number of equality atoms :   35 (  51 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1915)Refutation not found, incomplete strategy% (1915)------------------------------
% (1915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1915)Termination reason: Refutation not found, incomplete strategy

% (1915)Memory used [KB]: 1663
% (1915)Time elapsed: 0.104 s
% (1915)------------------------------
% (1915)------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f65])).

fof(f65,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f95,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(backward_demodulation,[],[f91,f94])).

fof(f94,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f66,f93,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f38,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f93,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(superposition,[],[f74,f86])).

fof(f86,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f66,f59,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f59,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f41,f36,f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f91,plain,(
    ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) ),
    inference(subsumption_resolution,[],[f90,f65])).

fof(f90,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) ),
    inference(backward_demodulation,[],[f85,f89])).

fof(f89,plain,(
    sK2 = k8_relat_1(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f66,f87,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f87,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f66,f60,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f60,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | ~ r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f73,f75])).

fof(f75,plain,(
    ! [X0] : k5_relat_1(sK2,k6_partfun1(X0)) = k8_relat_1(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f66,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f73,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) ),
    inference(backward_demodulation,[],[f72,f61])).

fof(f61,plain,(
    ! [X0] : k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) = k5_relat_1(sK2,k6_partfun1(X0)) ),
    inference(unit_resulting_resolution,[],[f54,f36,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f72,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    inference(backward_demodulation,[],[f37,f63])).

fof(f63,plain,(
    ! [X0] : k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) = k5_relat_1(k6_partfun1(X0),sK2) ),
    inference(unit_resulting_resolution,[],[f54,f36,f53])).

fof(f37,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (797605888)
% 0.14/0.37  ipcrm: permission denied for id (797671427)
% 0.14/0.38  ipcrm: permission denied for id (800620549)
% 0.14/0.38  ipcrm: permission denied for id (797736966)
% 0.14/0.38  ipcrm: permission denied for id (800686088)
% 0.14/0.38  ipcrm: permission denied for id (797769738)
% 0.14/0.38  ipcrm: permission denied for id (800751627)
% 0.14/0.39  ipcrm: permission denied for id (797802508)
% 0.14/0.39  ipcrm: permission denied for id (797835278)
% 0.14/0.39  ipcrm: permission denied for id (797868047)
% 0.14/0.39  ipcrm: permission denied for id (797900816)
% 0.14/0.39  ipcrm: permission denied for id (800817169)
% 0.14/0.39  ipcrm: permission denied for id (797933586)
% 0.14/0.39  ipcrm: permission denied for id (797966355)
% 0.14/0.40  ipcrm: permission denied for id (797999124)
% 0.14/0.40  ipcrm: permission denied for id (798031893)
% 0.14/0.40  ipcrm: permission denied for id (798064662)
% 0.14/0.40  ipcrm: permission denied for id (798097431)
% 0.14/0.40  ipcrm: permission denied for id (800882713)
% 0.14/0.41  ipcrm: permission denied for id (798261276)
% 0.14/0.41  ipcrm: permission denied for id (798294045)
% 0.14/0.41  ipcrm: permission denied for id (798326814)
% 0.14/0.41  ipcrm: permission denied for id (798359583)
% 0.14/0.41  ipcrm: permission denied for id (798392352)
% 0.14/0.41  ipcrm: permission denied for id (798425121)
% 0.14/0.41  ipcrm: permission denied for id (798457890)
% 0.14/0.41  ipcrm: permission denied for id (800981027)
% 0.14/0.42  ipcrm: permission denied for id (798490660)
% 0.14/0.42  ipcrm: permission denied for id (798523429)
% 0.14/0.42  ipcrm: permission denied for id (798556198)
% 0.14/0.42  ipcrm: permission denied for id (801013799)
% 0.22/0.42  ipcrm: permission denied for id (798621736)
% 0.22/0.42  ipcrm: permission denied for id (801112107)
% 0.22/0.43  ipcrm: permission denied for id (801177645)
% 0.22/0.43  ipcrm: permission denied for id (801243183)
% 0.22/0.43  ipcrm: permission denied for id (801308721)
% 0.22/0.43  ipcrm: permission denied for id (801341490)
% 0.22/0.44  ipcrm: permission denied for id (801374259)
% 0.22/0.44  ipcrm: permission denied for id (801407028)
% 0.22/0.44  ipcrm: permission denied for id (799014967)
% 0.22/0.44  ipcrm: permission denied for id (799047736)
% 0.22/0.44  ipcrm: permission denied for id (801505337)
% 0.22/0.45  ipcrm: permission denied for id (799080507)
% 0.22/0.45  ipcrm: permission denied for id (799113277)
% 0.22/0.45  ipcrm: permission denied for id (801603646)
% 0.22/0.45  ipcrm: permission denied for id (799146047)
% 0.22/0.45  ipcrm: permission denied for id (799178816)
% 0.22/0.45  ipcrm: permission denied for id (799211585)
% 0.22/0.45  ipcrm: permission denied for id (799244354)
% 0.22/0.46  ipcrm: permission denied for id (799277123)
% 0.22/0.46  ipcrm: permission denied for id (799309892)
% 0.22/0.46  ipcrm: permission denied for id (799342661)
% 0.22/0.46  ipcrm: permission denied for id (799375433)
% 0.22/0.46  ipcrm: permission denied for id (799408202)
% 0.22/0.47  ipcrm: permission denied for id (799440971)
% 0.22/0.47  ipcrm: permission denied for id (801734732)
% 0.22/0.47  ipcrm: permission denied for id (801800269)
% 0.22/0.47  ipcrm: permission denied for id (801833038)
% 0.22/0.47  ipcrm: permission denied for id (799506511)
% 0.22/0.47  ipcrm: permission denied for id (801865808)
% 0.22/0.47  ipcrm: permission denied for id (801898577)
% 0.22/0.47  ipcrm: permission denied for id (801931346)
% 0.22/0.48  ipcrm: permission denied for id (799572051)
% 0.22/0.48  ipcrm: permission denied for id (801996885)
% 0.22/0.48  ipcrm: permission denied for id (802095191)
% 0.22/0.48  ipcrm: permission denied for id (799637592)
% 0.22/0.48  ipcrm: permission denied for id (802127961)
% 0.22/0.48  ipcrm: permission denied for id (802160730)
% 0.22/0.49  ipcrm: permission denied for id (802291805)
% 0.22/0.49  ipcrm: permission denied for id (799703134)
% 0.22/0.49  ipcrm: permission denied for id (802324575)
% 0.22/0.49  ipcrm: permission denied for id (802390113)
% 0.22/0.49  ipcrm: permission denied for id (799768674)
% 0.22/0.50  ipcrm: permission denied for id (799834212)
% 0.22/0.50  ipcrm: permission denied for id (802455653)
% 0.22/0.50  ipcrm: permission denied for id (799932519)
% 0.22/0.50  ipcrm: permission denied for id (802521192)
% 0.22/0.50  ipcrm: permission denied for id (802553961)
% 0.22/0.51  ipcrm: permission denied for id (802652268)
% 0.22/0.51  ipcrm: permission denied for id (802685037)
% 0.22/0.51  ipcrm: permission denied for id (802717806)
% 0.22/0.51  ipcrm: permission denied for id (802783344)
% 0.22/0.51  ipcrm: permission denied for id (802816113)
% 0.22/0.51  ipcrm: permission denied for id (802848882)
% 0.22/0.52  ipcrm: permission denied for id (802979958)
% 0.22/0.52  ipcrm: permission denied for id (800292983)
% 0.22/0.52  ipcrm: permission denied for id (803045497)
% 0.22/0.52  ipcrm: permission denied for id (800391290)
% 0.22/0.53  ipcrm: permission denied for id (803078267)
% 0.22/0.53  ipcrm: permission denied for id (800456829)
% 0.22/0.53  ipcrm: permission denied for id (800489598)
% 0.22/0.53  ipcrm: permission denied for id (803143807)
% 0.91/0.66  % (1917)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.91/0.67  % (1925)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.68  % (1945)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.68  % (1934)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.68  % (1945)Refutation not found, incomplete strategy% (1945)------------------------------
% 1.34/0.68  % (1945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.69  % (1934)Refutation not found, incomplete strategy% (1934)------------------------------
% 1.34/0.69  % (1934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.69  % (1925)Refutation found. Thanks to Tanya!
% 1.34/0.69  % SZS status Theorem for theBenchmark
% 1.34/0.69  % (1945)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.69  
% 1.34/0.69  % (1945)Memory used [KB]: 6268
% 1.34/0.69  % (1945)Time elapsed: 0.111 s
% 1.34/0.69  % (1945)------------------------------
% 1.34/0.69  % (1945)------------------------------
% 1.34/0.69  % (1920)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.69  % (1919)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.69  % (1926)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.69  % (1915)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.70  % (1934)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.70  
% 1.34/0.70  % (1934)Memory used [KB]: 1791
% 1.34/0.70  % (1934)Time elapsed: 0.114 s
% 1.34/0.70  % (1934)------------------------------
% 1.34/0.70  % (1934)------------------------------
% 1.34/0.70  % SZS output start Proof for theBenchmark
% 1.34/0.70  % (1915)Refutation not found, incomplete strategy% (1915)------------------------------
% 1.34/0.70  % (1915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.70  % (1915)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.70  
% 1.34/0.70  % (1915)Memory used [KB]: 1663
% 1.34/0.70  % (1915)Time elapsed: 0.104 s
% 1.34/0.70  % (1915)------------------------------
% 1.34/0.70  % (1915)------------------------------
% 1.34/0.70  fof(f96,plain,(
% 1.34/0.70    $false),
% 1.34/0.70    inference(subsumption_resolution,[],[f95,f65])).
% 1.34/0.70  fof(f65,plain,(
% 1.34/0.70    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f36,f58])).
% 1.34/0.70  fof(f58,plain,(
% 1.34/0.70    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.34/0.70    inference(duplicate_literal_removal,[],[f57])).
% 1.34/0.70  fof(f57,plain,(
% 1.34/0.70    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.70    inference(equality_resolution,[],[f52])).
% 1.34/0.70  fof(f52,plain,(
% 1.34/0.70    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.70    inference(cnf_transformation,[],[f35])).
% 1.34/0.70  fof(f35,plain,(
% 1.34/0.70    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.70    inference(nnf_transformation,[],[f29])).
% 1.34/0.70  fof(f29,plain,(
% 1.34/0.70    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.70    inference(flattening,[],[f28])).
% 1.34/0.70  fof(f28,plain,(
% 1.34/0.70    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.34/0.70    inference(ennf_transformation,[],[f11])).
% 1.34/0.70  fof(f11,axiom,(
% 1.34/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.34/0.70  fof(f36,plain,(
% 1.34/0.70    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.34/0.70    inference(cnf_transformation,[],[f33])).
% 1.34/0.70  fof(f33,plain,(
% 1.34/0.70    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.34/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32])).
% 1.34/0.70  fof(f32,plain,(
% 1.34/0.70    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.34/0.70    introduced(choice_axiom,[])).
% 1.34/0.70  fof(f16,plain,(
% 1.34/0.70    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.70    inference(ennf_transformation,[],[f15])).
% 1.34/0.70  fof(f15,negated_conjecture,(
% 1.34/0.70    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 1.34/0.70    inference(negated_conjecture,[],[f14])).
% 1.34/0.70  fof(f14,conjecture,(
% 1.34/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 1.34/0.70  fof(f95,plain,(
% 1.34/0.70    ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.34/0.70    inference(backward_demodulation,[],[f91,f94])).
% 1.34/0.70  fof(f94,plain,(
% 1.34/0.70    sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f66,f93,f56])).
% 1.34/0.70  fof(f56,plain,(
% 1.34/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_partfun1(X0),X1) = X1) )),
% 1.34/0.70    inference(definition_unfolding,[],[f45,f38])).
% 1.34/0.70  fof(f38,plain,(
% 1.34/0.70    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.34/0.70    inference(cnf_transformation,[],[f13])).
% 1.34/0.70  fof(f13,axiom,(
% 1.34/0.70    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.34/0.70  fof(f45,plain,(
% 1.34/0.70    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.34/0.70    inference(cnf_transformation,[],[f23])).
% 1.34/0.70  fof(f23,plain,(
% 1.34/0.70    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(flattening,[],[f22])).
% 1.34/0.70  fof(f22,plain,(
% 1.34/0.70    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(ennf_transformation,[],[f7])).
% 1.34/0.70  fof(f7,axiom,(
% 1.34/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.34/0.70  fof(f93,plain,(
% 1.34/0.70    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.34/0.70    inference(superposition,[],[f74,f86])).
% 1.34/0.70  fof(f86,plain,(
% 1.34/0.70    sK2 = k7_relat_1(sK2,sK0)),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f66,f59,f48])).
% 1.34/0.70  fof(f48,plain,(
% 1.34/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.34/0.70    inference(cnf_transformation,[],[f26])).
% 1.34/0.70  fof(f26,plain,(
% 1.34/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(flattening,[],[f25])).
% 1.34/0.70  fof(f25,plain,(
% 1.34/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.34/0.70    inference(ennf_transformation,[],[f6])).
% 1.34/0.70  fof(f6,axiom,(
% 1.34/0.70    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.34/0.70  fof(f59,plain,(
% 1.34/0.70    v4_relat_1(sK2,sK0)),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f36,f49])).
% 1.34/0.70  fof(f49,plain,(
% 1.34/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.34/0.70    inference(cnf_transformation,[],[f27])).
% 1.34/0.70  fof(f27,plain,(
% 1.34/0.70    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.70    inference(ennf_transformation,[],[f9])).
% 1.34/0.70  fof(f9,axiom,(
% 1.34/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.70  fof(f74,plain,(
% 1.34/0.70    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f66,f42])).
% 1.34/0.70  fof(f42,plain,(
% 1.34/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.34/0.70    inference(cnf_transformation,[],[f18])).
% 1.34/0.70  fof(f18,plain,(
% 1.34/0.70    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(ennf_transformation,[],[f8])).
% 1.34/0.70  fof(f8,axiom,(
% 1.34/0.70    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.34/0.70  fof(f66,plain,(
% 1.34/0.70    v1_relat_1(sK2)),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f41,f36,f40])).
% 1.34/0.70  fof(f40,plain,(
% 1.34/0.70    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.34/0.70    inference(cnf_transformation,[],[f17])).
% 1.34/0.70  fof(f17,plain,(
% 1.34/0.70    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.70    inference(ennf_transformation,[],[f1])).
% 1.34/0.70  fof(f1,axiom,(
% 1.34/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.70  fof(f41,plain,(
% 1.34/0.70    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.70    inference(cnf_transformation,[],[f3])).
% 1.34/0.70  fof(f3,axiom,(
% 1.34/0.70    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.70  fof(f91,plain,(
% 1.34/0.70    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)),
% 1.34/0.70    inference(subsumption_resolution,[],[f90,f65])).
% 1.34/0.70  fof(f90,plain,(
% 1.34/0.70    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)),
% 1.34/0.70    inference(backward_demodulation,[],[f85,f89])).
% 1.34/0.70  fof(f89,plain,(
% 1.34/0.70    sK2 = k8_relat_1(sK1,sK2)),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f66,f87,f44])).
% 1.34/0.70  fof(f44,plain,(
% 1.34/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 1.34/0.70    inference(cnf_transformation,[],[f21])).
% 1.34/0.70  fof(f21,plain,(
% 1.34/0.70    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(flattening,[],[f20])).
% 1.34/0.70  fof(f20,plain,(
% 1.34/0.70    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(ennf_transformation,[],[f5])).
% 1.34/0.70  fof(f5,axiom,(
% 1.34/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.34/0.70  fof(f87,plain,(
% 1.34/0.70    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f66,f60,f46])).
% 1.34/0.70  fof(f46,plain,(
% 1.34/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.34/0.70    inference(cnf_transformation,[],[f34])).
% 1.34/0.70  fof(f34,plain,(
% 1.34/0.70    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(nnf_transformation,[],[f24])).
% 1.34/0.70  fof(f24,plain,(
% 1.34/0.70    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(ennf_transformation,[],[f2])).
% 1.34/0.70  fof(f2,axiom,(
% 1.34/0.70    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.34/0.70  fof(f60,plain,(
% 1.34/0.70    v5_relat_1(sK2,sK1)),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f36,f50])).
% 1.34/0.70  fof(f50,plain,(
% 1.34/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.34/0.70    inference(cnf_transformation,[],[f27])).
% 1.34/0.70  fof(f85,plain,(
% 1.34/0.70    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | ~r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2)),
% 1.34/0.70    inference(backward_demodulation,[],[f73,f75])).
% 1.34/0.70  fof(f75,plain,(
% 1.34/0.70    ( ! [X0] : (k5_relat_1(sK2,k6_partfun1(X0)) = k8_relat_1(X0,sK2)) )),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f66,f55])).
% 1.34/0.70  fof(f55,plain,(
% 1.34/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))) )),
% 1.34/0.70    inference(definition_unfolding,[],[f43,f38])).
% 1.34/0.70  fof(f43,plain,(
% 1.34/0.70    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.34/0.70    inference(cnf_transformation,[],[f19])).
% 1.34/0.70  fof(f19,plain,(
% 1.34/0.70    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.34/0.70    inference(ennf_transformation,[],[f4])).
% 1.34/0.70  fof(f4,axiom,(
% 1.34/0.70    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.34/0.70  fof(f73,plain,(
% 1.34/0.70    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)),
% 1.34/0.70    inference(backward_demodulation,[],[f72,f61])).
% 1.34/0.70  fof(f61,plain,(
% 1.34/0.70    ( ! [X0] : (k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) = k5_relat_1(sK2,k6_partfun1(X0))) )),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f54,f36,f53])).
% 1.34/0.70  fof(f53,plain,(
% 1.34/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.70    inference(cnf_transformation,[],[f31])).
% 1.34/0.70  fof(f31,plain,(
% 1.34/0.70    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.70    inference(flattening,[],[f30])).
% 1.34/0.70  fof(f30,plain,(
% 1.34/0.70    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.34/0.70    inference(ennf_transformation,[],[f10])).
% 1.34/0.70  fof(f10,axiom,(
% 1.34/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.34/0.70  fof(f54,plain,(
% 1.34/0.70    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.34/0.70    inference(definition_unfolding,[],[f39,f38])).
% 1.34/0.70  fof(f39,plain,(
% 1.34/0.70    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.34/0.70    inference(cnf_transformation,[],[f12])).
% 1.34/0.70  fof(f12,axiom,(
% 1.34/0.70    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.34/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.34/0.70  fof(f72,plain,(
% 1.34/0.70    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 1.34/0.70    inference(backward_demodulation,[],[f37,f63])).
% 1.34/0.70  fof(f63,plain,(
% 1.34/0.70    ( ! [X0] : (k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) = k5_relat_1(k6_partfun1(X0),sK2)) )),
% 1.34/0.70    inference(unit_resulting_resolution,[],[f54,f36,f53])).
% 1.34/0.70  fof(f37,plain,(
% 1.34/0.70    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 1.34/0.70    inference(cnf_transformation,[],[f33])).
% 1.34/0.70  % SZS output end Proof for theBenchmark
% 1.34/0.70  % (1925)------------------------------
% 1.34/0.70  % (1925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.70  % (1925)Termination reason: Refutation
% 1.34/0.70  
% 1.34/0.70  % (1925)Memory used [KB]: 6268
% 1.34/0.70  % (1925)Time elapsed: 0.114 s
% 1.34/0.70  % (1925)------------------------------
% 1.34/0.70  % (1925)------------------------------
% 1.34/0.70  % (1708)Success in time 0.332 s
%------------------------------------------------------------------------------
