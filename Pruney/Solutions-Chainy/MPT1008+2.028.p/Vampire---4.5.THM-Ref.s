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
% DateTime   : Thu Dec  3 13:04:12 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  119 (3510 expanded)
%              Number of leaves         :   18 ( 952 expanded)
%              Depth                    :   32
%              Number of atoms          :  273 (7244 expanded)
%              Number of equality atoms :  116 (3785 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(subsumption_resolution,[],[f337,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f337,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(subsumption_resolution,[],[f336,f46])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f336,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f329,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f329,plain,(
    k1_xboole_0 != k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f281,f328])).

fof(f328,plain,(
    k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(trivial_inequality_removal,[],[f327])).

fof(f327,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f246,f277])).

fof(f277,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f273,f236])).

fof(f236,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f235,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f235,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f234,f188])).

fof(f188,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f186,f77])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f42,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f186,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f177,f69])).

fof(f177,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f76,f176])).

fof(f176,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f154,f109])).

fof(f109,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f94,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(resolution,[],[f101,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f75,f75])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f101,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f100,f77])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(superposition,[],[f93,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sK2 = k7_relat_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f92,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f92,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f89,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f77,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f93,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X1)),X1) ),
    inference(resolution,[],[f89,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f94,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f154,plain,(
    ! [X3] :
      ( k1_relat_1(sK2) != k2_enumset1(X3,X3,X3,X3)
      | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) ) ),
    inference(subsumption_resolution,[],[f88,f89])).

fof(f88,plain,(
    ! [X3] :
      ( ~ v1_relat_1(sK2)
      | k1_relat_1(sK2) != k2_enumset1(X3,X3,X3,X3)
      | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) ) ),
    inference(resolution,[],[f40,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f53,f75,f75])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f44,f75,f75])).

fof(f44,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f234,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f233,f45])).

fof(f233,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f232,f188])).

fof(f232,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f207,f47])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(sK2) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f106,f188])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(sK2) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(superposition,[],[f96,f98])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK2,X0)))
      | k1_relat_1(k7_relat_1(sK2,X0)) = X0 ) ),
    inference(resolution,[],[f93,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f273,plain,(
    ! [X0] : r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X0) ),
    inference(resolution,[],[f272,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f272,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f271,f226])).

fof(f226,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f225,f45])).

fof(f225,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f224,f188])).

fof(f224,plain,(
    ! [X0] : r1_tarski(k1_relat_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f203,f47])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f100,f188])).

fof(f271,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f247,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f247,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(forward_demodulation,[],[f214,f46])).

fof(f214,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(backward_demodulation,[],[f171,f188])).

fof(f171,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(subsumption_resolution,[],[f170,f77])).

fof(f170,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ) ),
    inference(superposition,[],[f129,f69])).

fof(f129,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(subsumption_resolution,[],[f128,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f126,f78])).

fof(f78,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f41,f75])).

fof(f41,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(resolution,[],[f87,f77])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(sK2,X2),k2_relset_1(X0,X1,sK2)) ) ),
    inference(resolution,[],[f40,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f246,plain,(
    ! [X3] :
      ( k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)
      | k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3)) ) ),
    inference(forward_demodulation,[],[f245,f46])).

fof(f245,plain,(
    ! [X3] :
      ( k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3))
      | k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) ) ),
    inference(forward_demodulation,[],[f244,f188])).

fof(f244,plain,(
    ! [X3] :
      ( k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)
      | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) ) ),
    inference(forward_demodulation,[],[f212,f45])).

fof(f212,plain,(
    ! [X3] :
      ( k1_relat_1(k1_xboole_0) != k2_enumset1(X3,X3,X3,X3)
      | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) ) ),
    inference(backward_demodulation,[],[f154,f188])).

fof(f281,plain,(
    k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) != k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f190,f277])).

fof(f190,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f76,f188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:17:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (18214)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (18206)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (18198)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (18214)Refutation not found, incomplete strategy% (18214)------------------------------
% 0.20/0.52  % (18214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18214)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18214)Memory used [KB]: 10746
% 0.20/0.52  % (18214)Time elapsed: 0.059 s
% 0.20/0.52  % (18214)------------------------------
% 0.20/0.52  % (18214)------------------------------
% 0.20/0.53  % (18204)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (18202)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (18202)Refutation not found, incomplete strategy% (18202)------------------------------
% 0.20/0.54  % (18202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18202)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18202)Memory used [KB]: 10618
% 0.20/0.54  % (18202)Time elapsed: 0.126 s
% 0.20/0.54  % (18202)------------------------------
% 0.20/0.54  % (18202)------------------------------
% 0.20/0.54  % (18193)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (18195)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (18199)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (18197)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (18218)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (18194)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (18208)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (18210)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (18192)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (18221)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (18196)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (18200)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (18207)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (18209)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (18213)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (18217)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (18216)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (18220)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (18219)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (18201)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (18203)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (18205)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (18212)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (18203)Refutation not found, incomplete strategy% (18203)------------------------------
% 0.20/0.56  % (18203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18203)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18203)Memory used [KB]: 10746
% 0.20/0.56  % (18203)Time elapsed: 0.149 s
% 0.20/0.56  % (18203)------------------------------
% 0.20/0.56  % (18203)------------------------------
% 0.20/0.56  % (18211)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (18215)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.60/0.58  % (18213)Refutation found. Thanks to Tanya!
% 1.60/0.58  % SZS status Theorem for theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f338,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(subsumption_resolution,[],[f337,f47])).
% 1.60/0.59  fof(f47,plain,(
% 1.60/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f7])).
% 1.60/0.59  fof(f7,axiom,(
% 1.60/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.60/0.59  fof(f337,plain,(
% 1.60/0.59    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.60/0.59    inference(subsumption_resolution,[],[f336,f46])).
% 1.60/0.59  fof(f46,plain,(
% 1.60/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.60/0.59    inference(cnf_transformation,[],[f11])).
% 1.60/0.59  fof(f11,axiom,(
% 1.60/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.60/0.59  fof(f336,plain,(
% 1.60/0.59    k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.60/0.59    inference(superposition,[],[f329,f69])).
% 1.60/0.59  fof(f69,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f34])).
% 1.60/0.59  fof(f34,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.59    inference(ennf_transformation,[],[f18])).
% 1.60/0.59  fof(f18,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.60/0.59  fof(f329,plain,(
% 1.60/0.59    k1_xboole_0 != k2_relset_1(k1_xboole_0,sK1,k1_xboole_0)),
% 1.60/0.59    inference(backward_demodulation,[],[f281,f328])).
% 1.60/0.59  fof(f328,plain,(
% 1.60/0.59    k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.60/0.59    inference(trivial_inequality_removal,[],[f327])).
% 1.60/0.59  fof(f327,plain,(
% 1.60/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.60/0.59    inference(superposition,[],[f246,f277])).
% 1.60/0.59  fof(f277,plain,(
% 1.60/0.59    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.60/0.59    inference(resolution,[],[f273,f236])).
% 1.60/0.59  fof(f236,plain,(
% 1.60/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.60/0.59    inference(forward_demodulation,[],[f235,f45])).
% 1.60/0.59  fof(f45,plain,(
% 1.60/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.60/0.59    inference(cnf_transformation,[],[f11])).
% 1.60/0.59  fof(f235,plain,(
% 1.60/0.59    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 1.60/0.59    inference(forward_demodulation,[],[f234,f188])).
% 1.60/0.59  fof(f188,plain,(
% 1.60/0.59    k1_xboole_0 = sK2),
% 1.60/0.59    inference(subsumption_resolution,[],[f186,f77])).
% 1.60/0.59  fof(f77,plain,(
% 1.60/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.60/0.59    inference(definition_unfolding,[],[f42,f75])).
% 1.60/0.59  fof(f75,plain,(
% 1.60/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f48,f74])).
% 1.60/0.59  fof(f74,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f51,f67])).
% 1.60/0.59  fof(f67,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f5])).
% 1.60/0.59  fof(f5,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.59  fof(f51,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f4])).
% 1.60/0.59  fof(f4,axiom,(
% 1.60/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.59  fof(f48,plain,(
% 1.60/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f3])).
% 1.60/0.59  fof(f3,axiom,(
% 1.60/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.59  fof(f42,plain,(
% 1.60/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.60/0.59    inference(cnf_transformation,[],[f23])).
% 1.60/0.59  fof(f23,plain,(
% 1.60/0.59    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.60/0.59    inference(flattening,[],[f22])).
% 1.60/0.59  fof(f22,plain,(
% 1.60/0.59    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.60/0.59    inference(ennf_transformation,[],[f21])).
% 1.60/0.59  fof(f21,negated_conjecture,(
% 1.60/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.60/0.59    inference(negated_conjecture,[],[f20])).
% 1.60/0.59  fof(f20,conjecture,(
% 1.60/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.60/0.59  fof(f186,plain,(
% 1.60/0.59    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.60/0.59    inference(trivial_inequality_removal,[],[f185])).
% 1.60/0.59  fof(f185,plain,(
% 1.60/0.59    k2_relat_1(sK2) != k2_relat_1(sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.60/0.59    inference(superposition,[],[f177,f69])).
% 1.60/0.59  fof(f177,plain,(
% 1.60/0.59    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(superposition,[],[f76,f176])).
% 1.60/0.59  fof(f176,plain,(
% 1.60/0.59    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(trivial_inequality_removal,[],[f175])).
% 1.60/0.59  fof(f175,plain,(
% 1.60/0.59    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(superposition,[],[f154,f109])).
% 1.60/0.59  fof(f109,plain,(
% 1.60/0.59    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(trivial_inequality_removal,[],[f108])).
% 1.60/0.59  fof(f108,plain,(
% 1.60/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.60/0.59    inference(superposition,[],[f94,f103])).
% 1.60/0.59  fof(f103,plain,(
% 1.60/0.59    k1_xboole_0 = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.60/0.59    inference(resolution,[],[f101,f82])).
% 1.60/0.59  fof(f82,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.60/0.59    inference(definition_unfolding,[],[f61,f75,f75])).
% 1.60/0.59  fof(f61,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f6])).
% 1.60/0.59  fof(f6,axiom,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.60/0.59  fof(f101,plain,(
% 1.60/0.59    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.60/0.59    inference(resolution,[],[f100,f77])).
% 1.60/0.59  fof(f100,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k1_relat_1(sK2),X0)) )),
% 1.60/0.59    inference(superposition,[],[f93,f98])).
% 1.60/0.59  fof(f98,plain,(
% 1.60/0.59    ( ! [X0,X1] : (sK2 = k7_relat_1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.59    inference(resolution,[],[f92,f70])).
% 1.60/0.59  fof(f70,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f35])).
% 1.60/0.59  fof(f35,plain,(
% 1.60/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.59    inference(ennf_transformation,[],[f17])).
% 1.60/0.59  fof(f17,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.60/0.59  fof(f92,plain,(
% 1.60/0.59    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) )),
% 1.60/0.59    inference(resolution,[],[f89,f54])).
% 1.60/0.59  fof(f54,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f30])).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.60/0.59    inference(flattening,[],[f29])).
% 1.60/0.59  fof(f29,plain,(
% 1.60/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.60/0.59    inference(ennf_transformation,[],[f10])).
% 1.60/0.59  fof(f10,axiom,(
% 1.60/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.60/0.59  fof(f89,plain,(
% 1.60/0.59    v1_relat_1(sK2)),
% 1.60/0.59    inference(resolution,[],[f77,f68])).
% 1.60/0.59  fof(f68,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f33])).
% 1.60/0.59  fof(f33,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.59    inference(ennf_transformation,[],[f16])).
% 1.60/0.59  fof(f16,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.60/0.59  fof(f93,plain,(
% 1.60/0.59    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X1)),X1)) )),
% 1.60/0.59    inference(resolution,[],[f89,f52])).
% 1.60/0.59  fof(f52,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f26])).
% 1.60/0.59  fof(f26,plain,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f13])).
% 1.60/0.59  fof(f13,axiom,(
% 1.60/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.60/0.59  fof(f94,plain,(
% 1.60/0.59    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(resolution,[],[f89,f49])).
% 1.60/0.59  fof(f49,plain,(
% 1.60/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.60/0.59    inference(cnf_transformation,[],[f25])).
% 1.60/0.59  fof(f25,plain,(
% 1.60/0.59    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.60/0.59    inference(flattening,[],[f24])).
% 1.60/0.59  fof(f24,plain,(
% 1.60/0.59    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f12])).
% 1.60/0.59  fof(f12,axiom,(
% 1.60/0.59    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.60/0.59  fof(f154,plain,(
% 1.60/0.59    ( ! [X3] : (k1_relat_1(sK2) != k2_enumset1(X3,X3,X3,X3) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) )),
% 1.60/0.59    inference(subsumption_resolution,[],[f88,f89])).
% 1.60/0.59  fof(f88,plain,(
% 1.60/0.59    ( ! [X3] : (~v1_relat_1(sK2) | k1_relat_1(sK2) != k2_enumset1(X3,X3,X3,X3) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) )),
% 1.60/0.59    inference(resolution,[],[f40,f79])).
% 1.60/0.59  fof(f79,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f53,f75,f75])).
% 1.60/0.59  fof(f53,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f28])).
% 1.60/0.59  fof(f28,plain,(
% 1.60/0.59    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.60/0.59    inference(flattening,[],[f27])).
% 1.60/0.59  fof(f27,plain,(
% 1.60/0.59    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.60/0.59    inference(ennf_transformation,[],[f14])).
% 1.60/0.59  fof(f14,axiom,(
% 1.60/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.60/0.59  fof(f40,plain,(
% 1.60/0.59    v1_funct_1(sK2)),
% 1.60/0.59    inference(cnf_transformation,[],[f23])).
% 1.60/0.59  fof(f76,plain,(
% 1.60/0.59    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.60/0.59    inference(definition_unfolding,[],[f44,f75,f75])).
% 1.60/0.59  fof(f44,plain,(
% 1.60/0.59    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.60/0.59    inference(cnf_transformation,[],[f23])).
% 1.60/0.59  fof(f234,plain,(
% 1.60/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.60/0.59    inference(forward_demodulation,[],[f233,f45])).
% 1.60/0.59  fof(f233,plain,(
% 1.60/0.59    ( ! [X0] : (k1_relat_1(k1_xboole_0) = X0 | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.60/0.59    inference(forward_demodulation,[],[f232,f188])).
% 1.60/0.59  fof(f232,plain,(
% 1.60/0.59    ( ! [X0] : (k1_relat_1(sK2) = X0 | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.60/0.59    inference(subsumption_resolution,[],[f207,f47])).
% 1.60/0.59  fof(f207,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0 | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.60/0.59    inference(backward_demodulation,[],[f106,f188])).
% 1.60/0.59  fof(f106,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0 | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.60/0.59    inference(superposition,[],[f96,f98])).
% 1.60/0.59  fof(f96,plain,(
% 1.60/0.59    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k7_relat_1(sK2,X0))) | k1_relat_1(k7_relat_1(sK2,X0)) = X0) )),
% 1.60/0.59    inference(resolution,[],[f93,f57])).
% 1.60/0.59  fof(f57,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.59  fof(f273,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X0)) )),
% 1.60/0.59    inference(resolution,[],[f272,f59])).
% 1.60/0.59  fof(f59,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f31])).
% 1.60/0.59  fof(f31,plain,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f1])).
% 1.60/0.59  fof(f1,axiom,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.60/0.59  fof(f272,plain,(
% 1.60/0.59    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.60/0.59    inference(subsumption_resolution,[],[f271,f226])).
% 1.60/0.59  fof(f226,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.60/0.59    inference(forward_demodulation,[],[f225,f45])).
% 1.60/0.59  fof(f225,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 1.60/0.59    inference(forward_demodulation,[],[f224,f188])).
% 1.60/0.59  fof(f224,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0)) )),
% 1.60/0.59    inference(subsumption_resolution,[],[f203,f47])).
% 1.60/0.59  fof(f203,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k1_relat_1(sK2),X0)) )),
% 1.60/0.59    inference(backward_demodulation,[],[f100,f188])).
% 1.60/0.59  fof(f271,plain,(
% 1.60/0.59    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,X0))) )),
% 1.60/0.59    inference(resolution,[],[f247,f66])).
% 1.77/0.59  fof(f66,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f32])).
% 1.77/0.59  fof(f32,plain,(
% 1.77/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.77/0.59    inference(ennf_transformation,[],[f15])).
% 1.77/0.59  fof(f15,axiom,(
% 1.77/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.77/0.59  fof(f247,plain,(
% 1.77/0.59    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.77/0.59    inference(forward_demodulation,[],[f214,f46])).
% 1.77/0.59  fof(f214,plain,(
% 1.77/0.59    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.77/0.59    inference(backward_demodulation,[],[f171,f188])).
% 1.77/0.59  fof(f171,plain,(
% 1.77/0.59    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.77/0.59    inference(subsumption_resolution,[],[f170,f77])).
% 1.77/0.59  fof(f170,plain,(
% 1.77/0.59    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) )),
% 1.77/0.59    inference(superposition,[],[f129,f69])).
% 1.77/0.59  fof(f129,plain,(
% 1.77/0.59    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.77/0.59    inference(subsumption_resolution,[],[f128,f43])).
% 1.77/0.59  fof(f43,plain,(
% 1.77/0.59    k1_xboole_0 != sK1),
% 1.77/0.59    inference(cnf_transformation,[],[f23])).
% 1.77/0.59  fof(f128,plain,(
% 1.77/0.59    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 1.77/0.59    inference(subsumption_resolution,[],[f126,f78])).
% 1.77/0.59  fof(f78,plain,(
% 1.77/0.59    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.77/0.59    inference(definition_unfolding,[],[f41,f75])).
% 1.77/0.59  fof(f41,plain,(
% 1.77/0.59    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.77/0.59    inference(cnf_transformation,[],[f23])).
% 1.77/0.59  fof(f126,plain,(
% 1.77/0.59    ( ! [X0] : (~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 1.77/0.59    inference(resolution,[],[f87,f77])).
% 1.77/0.59  fof(f87,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(sK2,X2),k2_relset_1(X0,X1,sK2))) )),
% 1.77/0.59    inference(resolution,[],[f40,f73])).
% 1.77/0.59  fof(f73,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f39])).
% 1.77/0.59  fof(f39,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.77/0.59    inference(flattening,[],[f38])).
% 1.77/0.59  fof(f38,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.77/0.59    inference(ennf_transformation,[],[f19])).
% 1.77/0.59  fof(f19,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.77/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.77/0.59  fof(f246,plain,(
% 1.77/0.59    ( ! [X3] : (k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3))) )),
% 1.77/0.59    inference(forward_demodulation,[],[f245,f46])).
% 1.77/0.59  fof(f245,plain,(
% 1.77/0.59    ( ! [X3] : (k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3)) | k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)) )),
% 1.77/0.59    inference(forward_demodulation,[],[f244,f188])).
% 1.77/0.59  fof(f244,plain,(
% 1.77/0.59    ( ! [X3] : (k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) )),
% 1.77/0.59    inference(forward_demodulation,[],[f212,f45])).
% 1.77/0.59  fof(f212,plain,(
% 1.77/0.59    ( ! [X3] : (k1_relat_1(k1_xboole_0) != k2_enumset1(X3,X3,X3,X3) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) )),
% 1.77/0.59    inference(backward_demodulation,[],[f154,f188])).
% 1.77/0.59  fof(f281,plain,(
% 1.77/0.59    k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) != k2_relset_1(k1_xboole_0,sK1,k1_xboole_0)),
% 1.77/0.59    inference(backward_demodulation,[],[f190,f277])).
% 1.77/0.59  fof(f190,plain,(
% 1.77/0.59    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.77/0.59    inference(backward_demodulation,[],[f76,f188])).
% 1.77/0.59  % SZS output end Proof for theBenchmark
% 1.77/0.59  % (18213)------------------------------
% 1.77/0.59  % (18213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (18213)Termination reason: Refutation
% 1.77/0.59  
% 1.77/0.59  % (18213)Memory used [KB]: 1791
% 1.77/0.59  % (18213)Time elapsed: 0.149 s
% 1.77/0.59  % (18213)------------------------------
% 1.77/0.59  % (18213)------------------------------
% 1.77/0.59  % (18188)Success in time 0.225 s
%------------------------------------------------------------------------------
