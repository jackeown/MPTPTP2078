%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  120 (5887 expanded)
%              Number of leaves         :   19 (1598 expanded)
%              Depth                    :   38
%              Number of atoms          :  285 (12210 expanded)
%              Number of equality atoms :  132 (6412 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16116)Termination reason: Refutation not found, incomplete strategy

% (16116)Memory used [KB]: 10746
% (16116)Time elapsed: 0.142 s
% (16116)------------------------------
% (16116)------------------------------
fof(f346,plain,(
    $false ),
    inference(subsumption_resolution,[],[f345,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f345,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(trivial_inequality_removal,[],[f344])).

fof(f344,plain,
    ( k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f339,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f339,plain,(
    k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f298,f338])).

fof(f338,plain,(
    k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f337,f216])).

fof(f216,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f101,f206])).

fof(f206,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f204,f83])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f43,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
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

fof(f204,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f194,f67])).

fof(f194,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f82,f193])).

fof(f193,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f192,f101])).

fof(f192,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f130,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f130,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(sK2) != k1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | k2_relat_1(X2) = k2_enumset1(k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f85,f121])).

fof(f121,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f120,f101])).

fof(f120,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f119])).

fof(f119,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f49,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(resolution,[],[f109,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f81,f81])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f109,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f104,f108])).

fof(f108,plain,(
    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f107,f83])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f103,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f103,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f101,f54])).

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

fof(f104,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X1)),X1) ),
    inference(resolution,[],[f101,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f53,f81,f81])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f82,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f45,f81,f81])).

fof(f45,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f337,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f336,f259])).

fof(f259,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f226,f244])).

fof(f244,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f243,f47])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f222,f206])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f107,f206])).

fof(f226,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f112,f206])).

fof(f112,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,k1_xboole_0)) ),
    inference(resolution,[],[f105,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f105,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK2,X0)))
      | k1_relat_1(k7_relat_1(sK2,X0)) = X0 ) ),
    inference(resolution,[],[f104,f57])).

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

fof(f336,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f279,f212])).

fof(f212,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f41,f206])).

fof(f279,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0)) ) ),
    inference(superposition,[],[f85,f275])).

fof(f275,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f271,f263])).

fof(f263,plain,(
    ! [X2] : r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X2) ),
    inference(resolution,[],[f248,f59])).

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

fof(f248,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f233,f46])).

fof(f233,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(X0,sK5(k1_xboole_0,X0)))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(backward_demodulation,[],[f162,f206])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k4_tarski(X0,sK5(sK2,X0)))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f155,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f155,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(subsumption_resolution,[],[f154,f83])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) ) ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) ) ),
    inference(superposition,[],[f78,f149])).

fof(f149,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f99,f83])).

fof(f99,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(subsumption_resolution,[],[f98,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(resolution,[],[f84,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f84,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f42,f81])).

fof(f42,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f271,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f270,f259])).

fof(f270,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(forward_demodulation,[],[f256,f259])).

fof(f256,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f255,f57])).

fof(f255,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f219,f244])).

fof(f219,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(k1_xboole_0,X1)),X1) ),
    inference(backward_demodulation,[],[f104,f206])).

fof(f298,plain,(
    k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) != k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f213,f275])).

fof(f213,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f82,f206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (16103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (16109)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (16099)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (16124)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (16104)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (16111)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (16102)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (16109)Refutation not found, incomplete strategy% (16109)------------------------------
% 0.21/0.51  % (16109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16117)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (16109)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16109)Memory used [KB]: 10618
% 0.21/0.52  % (16109)Time elapsed: 0.103 s
% 0.21/0.52  % (16109)------------------------------
% 0.21/0.52  % (16109)------------------------------
% 0.21/0.52  % (16106)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (16101)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (16114)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (16120)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (16113)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (16126)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (16105)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (16100)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (16116)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (16128)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (16122)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (16123)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (16116)Refutation not found, incomplete strategy% (16116)------------------------------
% 0.21/0.54  % (16116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16115)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (16127)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (16108)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (16125)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (16120)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (16119)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (16112)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (16118)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (16110)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (16121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.56  % (16121)Refutation not found, incomplete strategy% (16121)------------------------------
% 1.53/0.56  % (16121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (16121)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (16121)Memory used [KB]: 10746
% 1.53/0.56  % (16121)Time elapsed: 0.153 s
% 1.53/0.56  % (16121)------------------------------
% 1.53/0.56  % (16121)------------------------------
% 1.53/0.56  % (16107)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.56  % SZS output start Proof for theBenchmark
% 1.53/0.56  % (16116)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (16116)Memory used [KB]: 10746
% 1.53/0.56  % (16116)Time elapsed: 0.142 s
% 1.53/0.56  % (16116)------------------------------
% 1.53/0.56  % (16116)------------------------------
% 1.53/0.56  fof(f346,plain,(
% 1.53/0.56    $false),
% 1.53/0.56    inference(subsumption_resolution,[],[f345,f47])).
% 1.53/0.56  fof(f47,plain,(
% 1.53/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f8])).
% 1.53/0.56  fof(f8,axiom,(
% 1.53/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.53/0.56  fof(f345,plain,(
% 1.53/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f344])).
% 1.53/0.56  fof(f344,plain,(
% 1.53/0.56    k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.53/0.56    inference(superposition,[],[f339,f67])).
% 1.53/0.56  fof(f67,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f34])).
% 1.53/0.56  fof(f34,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.56    inference(ennf_transformation,[],[f17])).
% 1.53/0.56  fof(f17,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.53/0.56  fof(f339,plain,(
% 1.53/0.56    k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k2_relat_1(k1_xboole_0)),
% 1.53/0.56    inference(backward_demodulation,[],[f298,f338])).
% 1.53/0.56  fof(f338,plain,(
% 1.53/0.56    k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) = k2_relat_1(k1_xboole_0)),
% 1.53/0.56    inference(subsumption_resolution,[],[f337,f216])).
% 1.53/0.56  fof(f216,plain,(
% 1.53/0.56    v1_relat_1(k1_xboole_0)),
% 1.53/0.56    inference(backward_demodulation,[],[f101,f206])).
% 1.53/0.56  fof(f206,plain,(
% 1.53/0.56    k1_xboole_0 = sK2),
% 1.53/0.56    inference(subsumption_resolution,[],[f204,f83])).
% 1.53/0.56  fof(f83,plain,(
% 1.53/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.53/0.56    inference(definition_unfolding,[],[f43,f81])).
% 1.53/0.56  fof(f81,plain,(
% 1.53/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.53/0.56    inference(definition_unfolding,[],[f48,f80])).
% 1.53/0.56  fof(f80,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.53/0.56    inference(definition_unfolding,[],[f51,f65])).
% 1.53/0.56  fof(f65,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f6])).
% 1.53/0.56  fof(f6,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.56  fof(f51,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f5])).
% 1.53/0.56  fof(f5,axiom,(
% 1.53/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.56  fof(f48,plain,(
% 1.53/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f4])).
% 1.53/0.56  fof(f4,axiom,(
% 1.53/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.56  fof(f43,plain,(
% 1.53/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.53/0.56    inference(cnf_transformation,[],[f23])).
% 1.53/0.56  fof(f23,plain,(
% 1.53/0.56    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.53/0.56    inference(flattening,[],[f22])).
% 1.53/0.56  fof(f22,plain,(
% 1.53/0.56    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.53/0.56    inference(ennf_transformation,[],[f21])).
% 1.53/0.56  fof(f21,negated_conjecture,(
% 1.53/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.53/0.56    inference(negated_conjecture,[],[f20])).
% 1.53/0.56  fof(f20,conjecture,(
% 1.53/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.53/0.56  fof(f204,plain,(
% 1.53/0.56    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f203])).
% 1.53/0.56  fof(f203,plain,(
% 1.53/0.56    k2_relat_1(sK2) != k2_relat_1(sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.53/0.56    inference(superposition,[],[f194,f67])).
% 1.53/0.56  fof(f194,plain,(
% 1.53/0.56    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.53/0.56    inference(superposition,[],[f82,f193])).
% 1.53/0.56  fof(f193,plain,(
% 1.53/0.56    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.53/0.56    inference(subsumption_resolution,[],[f192,f101])).
% 1.53/0.56  fof(f192,plain,(
% 1.53/0.56    ~v1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f191])).
% 1.53/0.56  fof(f191,plain,(
% 1.53/0.56    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.53/0.56    inference(resolution,[],[f130,f41])).
% 1.53/0.56  fof(f41,plain,(
% 1.53/0.56    v1_funct_1(sK2)),
% 1.53/0.56    inference(cnf_transformation,[],[f23])).
% 1.53/0.56  fof(f130,plain,(
% 1.53/0.56    ( ! [X2] : (~v1_funct_1(X2) | k1_relat_1(sK2) != k1_relat_1(X2) | ~v1_relat_1(X2) | k2_relat_1(X2) = k2_enumset1(k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0)) | k1_xboole_0 = sK2) )),
% 1.53/0.56    inference(superposition,[],[f85,f121])).
% 1.53/0.56  fof(f121,plain,(
% 1.53/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.53/0.56    inference(subsumption_resolution,[],[f120,f101])).
% 1.53/0.56  fof(f120,plain,(
% 1.53/0.56    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f119])).
% 1.53/0.56  fof(f119,plain,(
% 1.53/0.56    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.53/0.56    inference(superposition,[],[f49,f110])).
% 1.53/0.56  fof(f110,plain,(
% 1.53/0.56    k1_xboole_0 = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.53/0.56    inference(resolution,[],[f109,f88])).
% 1.53/0.56  fof(f88,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.53/0.56    inference(definition_unfolding,[],[f61,f81,f81])).
% 1.53/0.56  fof(f61,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f7])).
% 1.53/0.56  fof(f7,axiom,(
% 1.53/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.53/0.56  fof(f109,plain,(
% 1.53/0.56    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.53/0.56    inference(superposition,[],[f104,f108])).
% 1.53/0.56  fof(f108,plain,(
% 1.53/0.56    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.53/0.56    inference(resolution,[],[f107,f83])).
% 1.53/0.56  fof(f107,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = k7_relat_1(sK2,X0)) )),
% 1.53/0.56    inference(resolution,[],[f103,f68])).
% 1.53/0.56  fof(f68,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f35])).
% 1.53/0.56  fof(f35,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.56    inference(ennf_transformation,[],[f16])).
% 1.53/0.56  fof(f16,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.53/0.56  fof(f103,plain,(
% 1.53/0.56    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) )),
% 1.53/0.56    inference(resolution,[],[f101,f54])).
% 1.53/0.56  fof(f54,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.53/0.56    inference(cnf_transformation,[],[f30])).
% 1.53/0.56  fof(f30,plain,(
% 1.53/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.53/0.56    inference(flattening,[],[f29])).
% 1.53/0.56  fof(f29,plain,(
% 1.53/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.53/0.56    inference(ennf_transformation,[],[f10])).
% 1.53/0.56  fof(f10,axiom,(
% 1.53/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.53/0.56  fof(f104,plain,(
% 1.53/0.56    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X1)),X1)) )),
% 1.53/0.56    inference(resolution,[],[f101,f52])).
% 1.53/0.56  fof(f52,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  fof(f26,plain,(
% 1.53/0.56    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.53/0.56    inference(ennf_transformation,[],[f12])).
% 1.53/0.56  fof(f12,axiom,(
% 1.53/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.53/0.56  fof(f49,plain,(
% 1.53/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.53/0.56    inference(cnf_transformation,[],[f25])).
% 1.53/0.56  fof(f25,plain,(
% 1.53/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.53/0.56    inference(flattening,[],[f24])).
% 1.53/0.56  fof(f24,plain,(
% 1.53/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f11])).
% 1.53/0.56  fof(f11,axiom,(
% 1.53/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.53/0.56  fof(f85,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.53/0.56    inference(definition_unfolding,[],[f53,f81,f81])).
% 1.53/0.56  fof(f53,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f28])).
% 1.53/0.56  fof(f28,plain,(
% 1.53/0.56    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.53/0.56    inference(flattening,[],[f27])).
% 1.53/0.56  fof(f27,plain,(
% 1.53/0.56    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.53/0.56    inference(ennf_transformation,[],[f13])).
% 1.53/0.56  fof(f13,axiom,(
% 1.53/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.53/0.56  fof(f82,plain,(
% 1.53/0.56    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.53/0.56    inference(definition_unfolding,[],[f45,f81,f81])).
% 1.53/0.56  fof(f45,plain,(
% 1.53/0.56    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.53/0.56    inference(cnf_transformation,[],[f23])).
% 1.53/0.56  fof(f101,plain,(
% 1.53/0.56    v1_relat_1(sK2)),
% 1.53/0.56    inference(resolution,[],[f83,f66])).
% 1.53/0.56  fof(f66,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f33])).
% 1.53/0.56  fof(f33,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.56    inference(ennf_transformation,[],[f15])).
% 1.53/0.56  fof(f15,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.53/0.56  fof(f337,plain,(
% 1.53/0.56    ~v1_relat_1(k1_xboole_0) | k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) = k2_relat_1(k1_xboole_0)),
% 1.53/0.56    inference(subsumption_resolution,[],[f336,f259])).
% 1.53/0.56  fof(f259,plain,(
% 1.53/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.53/0.56    inference(forward_demodulation,[],[f226,f244])).
% 1.53/0.56  fof(f244,plain,(
% 1.53/0.56    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.53/0.56    inference(subsumption_resolution,[],[f243,f47])).
% 1.53/0.56  fof(f243,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.53/0.56    inference(forward_demodulation,[],[f222,f206])).
% 1.53/0.56  fof(f222,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.56    inference(backward_demodulation,[],[f107,f206])).
% 1.53/0.56  fof(f226,plain,(
% 1.53/0.56    k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0))),
% 1.53/0.56    inference(backward_demodulation,[],[f112,f206])).
% 1.53/0.56  fof(f112,plain,(
% 1.53/0.56    k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,k1_xboole_0))),
% 1.53/0.56    inference(resolution,[],[f105,f46])).
% 1.53/0.56  fof(f46,plain,(
% 1.53/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f3])).
% 1.53/0.56  fof(f3,axiom,(
% 1.53/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.53/0.56  fof(f105,plain,(
% 1.53/0.56    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k7_relat_1(sK2,X0))) | k1_relat_1(k7_relat_1(sK2,X0)) = X0) )),
% 1.53/0.56    inference(resolution,[],[f104,f57])).
% 1.53/0.56  fof(f57,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.53/0.56    inference(cnf_transformation,[],[f2])).
% 1.53/0.56  fof(f2,axiom,(
% 1.53/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.56  fof(f336,plain,(
% 1.53/0.56    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) = k2_relat_1(k1_xboole_0)),
% 1.53/0.56    inference(resolution,[],[f279,f212])).
% 1.53/0.56  fof(f212,plain,(
% 1.53/0.56    v1_funct_1(k1_xboole_0)),
% 1.53/0.56    inference(backward_demodulation,[],[f41,f206])).
% 1.53/0.56  fof(f279,plain,(
% 1.53/0.56    ( ! [X0] : (~v1_funct_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0))) )),
% 1.53/0.56    inference(superposition,[],[f85,f275])).
% 1.53/0.56  fof(f275,plain,(
% 1.53/0.56    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.53/0.56    inference(resolution,[],[f271,f263])).
% 1.53/0.56  fof(f263,plain,(
% 1.53/0.56    ( ! [X2] : (r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X2)) )),
% 1.53/0.56    inference(resolution,[],[f248,f59])).
% 1.53/0.56  fof(f59,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f31])).
% 1.53/0.56  fof(f31,plain,(
% 1.53/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f1])).
% 1.53/0.56  fof(f1,axiom,(
% 1.53/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.56  fof(f248,plain,(
% 1.53/0.56    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.53/0.56    inference(subsumption_resolution,[],[f233,f46])).
% 1.53/0.56  fof(f233,plain,(
% 1.53/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k4_tarski(X0,sK5(k1_xboole_0,X0))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.53/0.56    inference(backward_demodulation,[],[f162,f206])).
% 1.53/0.56  fof(f162,plain,(
% 1.53/0.56    ( ! [X0] : (~r1_tarski(sK2,k4_tarski(X0,sK5(sK2,X0))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.53/0.56    inference(resolution,[],[f155,f64])).
% 1.53/0.56  fof(f64,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f32])).
% 1.53/0.56  fof(f32,plain,(
% 1.53/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.53/0.56    inference(ennf_transformation,[],[f14])).
% 1.53/0.56  fof(f14,axiom,(
% 1.53/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.53/0.56  fof(f155,plain,(
% 1.53/0.56    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.53/0.56    inference(subsumption_resolution,[],[f154,f83])).
% 1.53/0.56  fof(f154,plain,(
% 1.53/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)) )),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f151])).
% 1.53/0.56  fof(f151,plain,(
% 1.53/0.56    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)) )),
% 1.53/0.56    inference(superposition,[],[f78,f149])).
% 1.53/0.56  fof(f149,plain,(
% 1.53/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.53/0.56    inference(subsumption_resolution,[],[f99,f83])).
% 1.53/0.56  fof(f99,plain,(
% 1.53/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.53/0.56    inference(subsumption_resolution,[],[f98,f44])).
% 1.53/0.56  fof(f44,plain,(
% 1.53/0.56    k1_xboole_0 != sK1),
% 1.53/0.56    inference(cnf_transformation,[],[f23])).
% 1.53/0.56  fof(f98,plain,(
% 1.53/0.56    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.53/0.56    inference(resolution,[],[f84,f75])).
% 1.53/0.56  fof(f75,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f37])).
% 1.53/0.56  fof(f37,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.56    inference(flattening,[],[f36])).
% 1.53/0.56  fof(f36,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.56    inference(ennf_transformation,[],[f19])).
% 1.53/0.56  fof(f19,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.53/0.56  fof(f84,plain,(
% 1.53/0.56    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.53/0.56    inference(definition_unfolding,[],[f42,f81])).
% 1.53/0.56  fof(f42,plain,(
% 1.53/0.56    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.53/0.56    inference(cnf_transformation,[],[f23])).
% 1.53/0.56  fof(f78,plain,(
% 1.53/0.56    ( ! [X2,X0,X3,X1] : (k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f38])).
% 1.53/0.56  fof(f38,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.53/0.56    inference(ennf_transformation,[],[f18])).
% 1.53/0.56  fof(f18,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.53/0.56  fof(f271,plain,(
% 1.53/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.53/0.56    inference(forward_demodulation,[],[f270,f259])).
% 1.53/0.56  fof(f270,plain,(
% 1.53/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_relat_1(k1_xboole_0) = X0) )),
% 1.53/0.56    inference(forward_demodulation,[],[f256,f259])).
% 1.53/0.56  fof(f256,plain,(
% 1.53/0.56    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0) = X0) )),
% 1.53/0.56    inference(resolution,[],[f255,f57])).
% 1.53/0.56  fof(f255,plain,(
% 1.53/0.56    ( ! [X1] : (r1_tarski(k1_relat_1(k1_xboole_0),X1)) )),
% 1.53/0.56    inference(forward_demodulation,[],[f219,f244])).
% 1.53/0.56  fof(f219,plain,(
% 1.53/0.56    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(k1_xboole_0,X1)),X1)) )),
% 1.53/0.56    inference(backward_demodulation,[],[f104,f206])).
% 1.53/0.56  fof(f298,plain,(
% 1.53/0.56    k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) != k2_relset_1(k1_xboole_0,sK1,k1_xboole_0)),
% 1.53/0.56    inference(forward_demodulation,[],[f213,f275])).
% 1.53/0.56  fof(f213,plain,(
% 1.53/0.56    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.53/0.56    inference(backward_demodulation,[],[f82,f206])).
% 1.53/0.56  % SZS output end Proof for theBenchmark
% 1.53/0.56  % (16120)------------------------------
% 1.53/0.56  % (16120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (16120)Termination reason: Refutation
% 1.53/0.56  
% 1.53/0.56  % (16120)Memory used [KB]: 1791
% 1.53/0.56  % (16120)Time elapsed: 0.113 s
% 1.53/0.56  % (16120)------------------------------
% 1.53/0.56  % (16120)------------------------------
% 1.53/0.56  % (16098)Success in time 0.198 s
%------------------------------------------------------------------------------
