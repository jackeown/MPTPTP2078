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
% DateTime   : Thu Dec  3 13:04:21 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 789 expanded)
%              Number of leaves         :   12 ( 205 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 (1934 expanded)
%              Number of equality atoms :   82 ( 996 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5829)Termination reason: Refutation not found, incomplete strategy
fof(f148,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f26,f60,f103,f75,f50])).

% (5825)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (5829)Memory used [KB]: 10746
fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f31,f46,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

% (5829)Time elapsed: 0.108 s
fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f75,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f73,f74])).

fof(f74,plain,(
    k2_relat_1(sK2) = k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) ),
    inference(forward_demodulation,[],[f58,f69])).

fof(f69,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f59,f61])).

fof(f61,plain,(
    ! [X0] : k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f59,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f26,f29,f49,f48,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

% (5829)------------------------------
% (5829)------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f49,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f27,f46])).

fof(f27,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f73,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) ),
    inference(backward_demodulation,[],[f47,f69])).

fof(f47,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f30,f46,f46])).

fof(f30,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f69,f102])).

fof(f102,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f83,f100])).

fof(f100,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f60,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f83,plain,(
    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f82,f77])).

fof(f77,plain,(
    k10_relat_1(sK2,sK1) = k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) ),
    inference(forward_demodulation,[],[f76,f70])).

fof(f70,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,X0) ),
    inference(backward_demodulation,[],[f61,f69])).

fof(f76,plain,(
    k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,sK1) = k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) ),
    inference(forward_demodulation,[],[f57,f69])).

fof(f57,plain,(
    k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f48,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f82,plain,(
    k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f81,f70])).

fof(f81,plain,(
    k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f80,f79])).

fof(f79,plain,(
    k2_relat_1(sK2) = k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f78,f74])).

fof(f78,plain,(
    k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f56,f69])).

fof(f56,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1))) ),
    inference(forward_demodulation,[],[f55,f69])).

fof(f55,plain,(
    k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,k2_enumset1(sK0,sK0,sK0,sK0))) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f60,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f48,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n025.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 20:57:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.19/0.52  % (5829)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.19/0.53  % (5821)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.53  % (5828)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.53  % (5826)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.53  % (5832)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.53  % (5824)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.19/0.53  % (5829)Refutation not found, incomplete strategy% (5829)------------------------------
% 1.19/0.53  % (5829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (5824)Refutation found. Thanks to Tanya!
% 1.19/0.53  % SZS status Theorem for theBenchmark
% 1.19/0.53  % SZS output start Proof for theBenchmark
% 1.19/0.53  % (5829)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.53  fof(f148,plain,(
% 1.19/0.53    $false),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f26,f60,f103,f75,f50])).
% 1.19/0.53  
% 1.19/0.53  % (5825)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.53  % (5829)Memory used [KB]: 10746
% 1.19/0.53  fof(f50,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.19/0.53    inference(definition_unfolding,[],[f31,f46,f46])).
% 1.19/0.53  fof(f46,plain,(
% 1.19/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.19/0.53    inference(definition_unfolding,[],[f39,f45])).
% 1.19/0.53  fof(f45,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.19/0.53    inference(definition_unfolding,[],[f43,f44])).
% 1.19/0.53  fof(f44,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f3])).
% 1.19/0.53  % (5829)Time elapsed: 0.108 s
% 1.19/0.53  fof(f3,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.19/0.53  fof(f43,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f2])).
% 1.19/0.53  fof(f2,axiom,(
% 1.19/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.19/0.53  fof(f39,plain,(
% 1.19/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f1])).
% 1.19/0.53  fof(f1,axiom,(
% 1.19/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.19/0.53  fof(f31,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f17])).
% 1.19/0.53  fof(f17,plain,(
% 1.19/0.53    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.19/0.53    inference(flattening,[],[f16])).
% 1.19/0.53  fof(f16,plain,(
% 1.19/0.53    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.19/0.53    inference(ennf_transformation,[],[f5])).
% 1.19/0.53  fof(f5,axiom,(
% 1.19/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.19/0.53  fof(f75,plain,(
% 1.19/0.53    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 1.19/0.53    inference(backward_demodulation,[],[f73,f74])).
% 1.19/0.53  fof(f74,plain,(
% 1.19/0.53    k2_relat_1(sK2) = k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2)),
% 1.19/0.53    inference(forward_demodulation,[],[f58,f69])).
% 1.19/0.53  fof(f69,plain,(
% 1.19/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1)),
% 1.19/0.53    inference(forward_demodulation,[],[f59,f61])).
% 1.19/0.53  fof(f61,plain,(
% 1.19/0.53    ( ! [X0] : (k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f48,f42])).
% 1.19/0.53  fof(f42,plain,(
% 1.19/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f25])).
% 1.19/0.53  fof(f25,plain,(
% 1.19/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f8])).
% 1.19/0.53  fof(f8,axiom,(
% 1.19/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.19/0.53  fof(f48,plain,(
% 1.19/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.19/0.53    inference(definition_unfolding,[],[f28,f46])).
% 1.19/0.53  fof(f28,plain,(
% 1.19/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.19/0.53    inference(cnf_transformation,[],[f15])).
% 1.19/0.53  fof(f15,plain,(
% 1.19/0.53    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.19/0.53    inference(flattening,[],[f14])).
% 1.19/0.53  fof(f14,plain,(
% 1.19/0.53    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.19/0.53    inference(ennf_transformation,[],[f13])).
% 1.19/0.53  fof(f13,negated_conjecture,(
% 1.19/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.19/0.53    inference(negated_conjecture,[],[f12])).
% 1.19/0.53  fof(f12,conjecture,(
% 1.19/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.19/0.53  fof(f59,plain,(
% 1.19/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1)),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f26,f29,f49,f48,f37])).
% 1.19/0.53  fof(f37,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 1.19/0.53    inference(cnf_transformation,[],[f22])).
% 1.19/0.53  fof(f22,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.19/0.53    inference(flattening,[],[f21])).
% 1.19/0.53  fof(f21,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.19/0.53    inference(ennf_transformation,[],[f11])).
% 1.19/0.53  % (5829)------------------------------
% 1.19/0.53  % (5829)------------------------------
% 1.19/0.53  fof(f11,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 1.19/0.53  fof(f49,plain,(
% 1.19/0.53    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.19/0.53    inference(definition_unfolding,[],[f27,f46])).
% 1.19/0.53  fof(f27,plain,(
% 1.19/0.53    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.19/0.53    inference(cnf_transformation,[],[f15])).
% 1.19/0.53  fof(f29,plain,(
% 1.19/0.53    k1_xboole_0 != sK1),
% 1.19/0.53    inference(cnf_transformation,[],[f15])).
% 1.19/0.53  fof(f58,plain,(
% 1.19/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f48,f36])).
% 1.19/0.53  fof(f36,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f20])).
% 1.19/0.53  fof(f20,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f7])).
% 1.19/0.53  fof(f7,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.19/0.53  fof(f73,plain,(
% 1.19/0.53    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2)),
% 1.19/0.53    inference(backward_demodulation,[],[f47,f69])).
% 1.19/0.53  fof(f47,plain,(
% 1.19/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.19/0.53    inference(definition_unfolding,[],[f30,f46,f46])).
% 1.19/0.53  fof(f30,plain,(
% 1.19/0.53    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.19/0.53    inference(cnf_transformation,[],[f15])).
% 1.19/0.53  fof(f103,plain,(
% 1.19/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.19/0.53    inference(backward_demodulation,[],[f69,f102])).
% 1.19/0.53  fof(f102,plain,(
% 1.19/0.53    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 1.19/0.53    inference(backward_demodulation,[],[f83,f100])).
% 1.19/0.53  fof(f100,plain,(
% 1.19/0.53    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f60,f40])).
% 1.19/0.53  fof(f40,plain,(
% 1.19/0.53    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f23])).
% 1.19/0.53  fof(f23,plain,(
% 1.19/0.53    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.53    inference(ennf_transformation,[],[f4])).
% 1.19/0.53  fof(f4,axiom,(
% 1.19/0.53    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.19/0.53  fof(f83,plain,(
% 1.19/0.53    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.19/0.53    inference(forward_demodulation,[],[f82,f77])).
% 1.19/0.53  fof(f77,plain,(
% 1.19/0.53    k10_relat_1(sK2,sK1) = k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2)),
% 1.19/0.53    inference(forward_demodulation,[],[f76,f70])).
% 1.19/0.53  fof(f70,plain,(
% 1.19/0.53    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,X0)) )),
% 1.19/0.53    inference(backward_demodulation,[],[f61,f69])).
% 1.19/0.53  fof(f76,plain,(
% 1.19/0.53    k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,sK1) = k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2)),
% 1.19/0.53    inference(forward_demodulation,[],[f57,f69])).
% 1.19/0.53  fof(f57,plain,(
% 1.19/0.53    k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f48,f35])).
% 1.19/0.53  fof(f35,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f19,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f9])).
% 1.19/0.53  fof(f9,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.19/0.53  fof(f82,plain,(
% 1.19/0.53    k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.19/0.53    inference(forward_demodulation,[],[f81,f70])).
% 1.19/0.53  fof(f81,plain,(
% 1.19/0.53    k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k2_relat_1(sK2))),
% 1.19/0.53    inference(forward_demodulation,[],[f80,f79])).
% 1.19/0.53  fof(f79,plain,(
% 1.19/0.53    k2_relat_1(sK2) = k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1))),
% 1.19/0.53    inference(forward_demodulation,[],[f78,f74])).
% 1.19/0.53  fof(f78,plain,(
% 1.19/0.53    k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1))),
% 1.19/0.53    inference(forward_demodulation,[],[f56,f69])).
% 1.19/0.53  fof(f56,plain,(
% 1.19/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f48,f34])).
% 1.19/0.53  fof(f34,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f80,plain,(
% 1.19/0.53    k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1)))),
% 1.19/0.53    inference(forward_demodulation,[],[f55,f69])).
% 1.19/0.53  fof(f55,plain,(
% 1.19/0.53    k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,k2_enumset1(sK0,sK0,sK0,sK0))) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f48,f33])).
% 1.19/0.53  fof(f33,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f18])).
% 1.19/0.53  fof(f18,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/0.53    inference(ennf_transformation,[],[f10])).
% 1.19/0.53  fof(f10,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 1.19/0.53  fof(f60,plain,(
% 1.19/0.53    v1_relat_1(sK2)),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f48,f41])).
% 1.19/0.53  fof(f41,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f24])).
% 1.19/0.53  fof(f24,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f6])).
% 1.19/0.53  fof(f6,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.19/0.53  fof(f26,plain,(
% 1.19/0.53    v1_funct_1(sK2)),
% 1.19/0.53    inference(cnf_transformation,[],[f15])).
% 1.19/0.53  % SZS output end Proof for theBenchmark
% 1.19/0.53  % (5824)------------------------------
% 1.19/0.53  % (5824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (5824)Termination reason: Refutation
% 1.19/0.53  
% 1.19/0.53  % (5824)Memory used [KB]: 6268
% 1.19/0.53  % (5824)Time elapsed: 0.120 s
% 1.19/0.53  % (5824)------------------------------
% 1.19/0.53  % (5824)------------------------------
% 1.19/0.54  % (5823)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.54  % (5819)Success in time 0.164 s
%------------------------------------------------------------------------------
