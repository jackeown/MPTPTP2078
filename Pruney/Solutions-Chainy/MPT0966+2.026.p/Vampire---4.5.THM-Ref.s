%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:41 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  126 (16201 expanded)
%              Number of leaves         :   14 (3340 expanded)
%              Depth                    :   37
%              Number of atoms          :  312 (75226 expanded)
%              Number of equality atoms :  133 (18558 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f520,plain,(
    $false ),
    inference(subsumption_resolution,[],[f517,f418])).

fof(f418,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f372,f414])).

fof(f414,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f413,f374])).

fof(f374,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f337,f361])).

fof(f361,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f360,f61])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f360,plain,(
    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f359,f269])).

fof(f269,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f267,f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f267,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f219,f97])).

fof(f97,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f73,f71])).

fof(f71,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f70,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f32,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f32,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f33,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f219,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f80,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f140,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f140,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f83,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f123,f97])).

fof(f123,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f69,f115,f122])).

fof(f122,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(forward_demodulation,[],[f118,f117])).

fof(f117,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f115,f56])).

fof(f118,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f115,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f115,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f90,f78])).

fof(f78,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f34,f75])).

fof(f75,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f34,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f87,f79])).

fof(f79,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f76,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f76,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(resolution,[],[f85,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f85,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f84,f79])).

fof(f84,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f72,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f72,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f33,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f69,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f29,f31])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f80,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f359,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f358,f43])).

fof(f358,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f282,f61])).

fof(f282,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f92,f269])).

fof(f92,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f77,f40])).

fof(f77,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f337,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f336,f269])).

fof(f336,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f280,f43])).

fof(f280,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f89,f269])).

fof(f89,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f85,f40])).

fof(f413,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f294,f361])).

fof(f294,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f123,f269])).

fof(f372,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f334,f361])).

fof(f334,plain,(
    ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f333,f331])).

fof(f331,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f271,f61])).

fof(f271,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f33,f269])).

fof(f333,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f332,f61])).

fof(f332,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f272,f269])).

fof(f272,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f69,f269])).

fof(f517,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f368,f512])).

fof(f512,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f509,f418])).

fof(f509,plain,(
    ! [X8] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X8)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f502,f507])).

fof(f507,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f499,f374])).

fof(f499,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK1
      | k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0) ) ),
    inference(resolution,[],[f401,f56])).

fof(f401,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f400,f361])).

fof(f400,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f399,f43])).

fof(f399,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f398,f376])).

fof(f376,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f342,f361])).

fof(f342,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f338])).

fof(f338,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f81,f337])).

fof(f81,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f79,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f398,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f397,f361])).

fof(f397,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f287,f43])).

fof(f287,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(backward_demodulation,[],[f104,f269])).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f102,f79])).

fof(f102,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f44,f97])).

fof(f502,plain,(
    ! [X8] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X8,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X8) ) ),
    inference(resolution,[],[f401,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f368,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f270,f361])).

fof(f270,plain,(
    v1_funct_2(sK3,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f32,f269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:03:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (10423)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.49  % (10414)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (10402)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (10427)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (10405)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (10417)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (10403)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (10408)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (10413)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.28/0.52  % (10412)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.28/0.52  % (10409)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.28/0.52  % (10418)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.28/0.53  % (10404)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.28/0.53  % (10422)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.28/0.53  % (10405)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f520,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(subsumption_resolution,[],[f517,f418])).
% 1.28/0.53  fof(f418,plain,(
% 1.28/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.28/0.53    inference(backward_demodulation,[],[f372,f414])).
% 1.28/0.53  fof(f414,plain,(
% 1.28/0.53    k1_xboole_0 = sK2),
% 1.28/0.53    inference(subsumption_resolution,[],[f413,f374])).
% 1.28/0.53  fof(f374,plain,(
% 1.28/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.28/0.53    inference(backward_demodulation,[],[f337,f361])).
% 1.28/0.53  fof(f361,plain,(
% 1.28/0.53    k1_xboole_0 = sK3),
% 1.28/0.53    inference(forward_demodulation,[],[f360,f61])).
% 1.28/0.53  fof(f61,plain,(
% 1.28/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.28/0.53    inference(equality_resolution,[],[f36])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.28/0.53  fof(f360,plain,(
% 1.28/0.53    sK3 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.28/0.53    inference(forward_demodulation,[],[f359,f269])).
% 1.28/0.53  fof(f269,plain,(
% 1.28/0.53    k1_xboole_0 = sK0),
% 1.28/0.53    inference(subsumption_resolution,[],[f267,f30])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.28/0.53    inference(flattening,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.28/0.53    inference(ennf_transformation,[],[f15])).
% 1.28/0.53  fof(f15,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.28/0.53    inference(negated_conjecture,[],[f14])).
% 1.28/0.53  fof(f14,conjecture,(
% 1.28/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 1.28/0.53  fof(f267,plain,(
% 1.28/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(duplicate_literal_removal,[],[f255])).
% 1.28/0.53  fof(f255,plain,(
% 1.28/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(superposition,[],[f219,f97])).
% 1.28/0.53  fof(f97,plain,(
% 1.28/0.53    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.28/0.53    inference(superposition,[],[f73,f71])).
% 1.28/0.53  fof(f71,plain,(
% 1.28/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.28/0.53    inference(subsumption_resolution,[],[f70,f33])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f70,plain,(
% 1.28/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.53    inference(resolution,[],[f32,f55])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    inference(flattening,[],[f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    inference(ennf_transformation,[],[f13])).
% 1.28/0.53  fof(f13,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    v1_funct_2(sK3,sK0,sK1)),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f73,plain,(
% 1.28/0.53    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.28/0.53    inference(resolution,[],[f33,f56])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    inference(ennf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.28/0.53  fof(f219,plain,(
% 1.28/0.53    k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f208])).
% 1.28/0.53  fof(f208,plain,(
% 1.28/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.28/0.53    inference(superposition,[],[f80,f147])).
% 1.28/0.53  fof(f147,plain,(
% 1.28/0.53    k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.28/0.53    inference(subsumption_resolution,[],[f140,f43])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.28/0.53  fof(f140,plain,(
% 1.28/0.53    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.28/0.53    inference(superposition,[],[f83,f136])).
% 1.28/0.53  fof(f136,plain,(
% 1.28/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f135])).
% 1.28/0.53  fof(f135,plain,(
% 1.28/0.53    sK0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(superposition,[],[f123,f97])).
% 1.28/0.53  fof(f123,plain,(
% 1.28/0.53    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.28/0.53    inference(global_subsumption,[],[f69,f115,f122])).
% 1.28/0.53  fof(f122,plain,(
% 1.28/0.53    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2)),
% 1.28/0.53    inference(forward_demodulation,[],[f118,f117])).
% 1.28/0.53  fof(f117,plain,(
% 1.28/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 1.28/0.53    inference(resolution,[],[f115,f56])).
% 1.28/0.53  fof(f118,plain,(
% 1.28/0.53    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | v1_funct_2(sK3,sK0,sK2)),
% 1.28/0.53    inference(resolution,[],[f115,f54])).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f25])).
% 1.28/0.53  fof(f115,plain,(
% 1.28/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.28/0.53    inference(resolution,[],[f90,f78])).
% 1.28/0.53  fof(f78,plain,(
% 1.28/0.53    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.28/0.53    inference(backward_demodulation,[],[f34,f75])).
% 1.28/0.53  fof(f75,plain,(
% 1.28/0.53    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.28/0.53    inference(resolution,[],[f33,f47])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    inference(ennf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f90,plain,(
% 1.28/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f87,f79])).
% 1.28/0.53  fof(f79,plain,(
% 1.28/0.53    v1_relat_1(sK3)),
% 1.28/0.53    inference(subsumption_resolution,[],[f76,f49])).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.28/0.53  fof(f76,plain,(
% 1.28/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 1.28/0.53    inference(resolution,[],[f33,f48])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.28/0.53  fof(f87,plain,(
% 1.28/0.53    ( ! [X0] : (~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.28/0.53    inference(resolution,[],[f85,f44])).
% 1.28/0.53  fof(f44,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f21])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.28/0.53    inference(flattening,[],[f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.28/0.53    inference(ennf_transformation,[],[f12])).
% 1.28/0.53  fof(f12,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.28/0.53  fof(f85,plain,(
% 1.28/0.53    r1_tarski(k1_relat_1(sK3),sK0)),
% 1.28/0.53    inference(subsumption_resolution,[],[f84,f79])).
% 1.28/0.53  fof(f84,plain,(
% 1.28/0.53    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 1.28/0.53    inference(resolution,[],[f72,f58])).
% 1.28/0.53  fof(f58,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f27])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.28/0.53  fof(f72,plain,(
% 1.28/0.53    v4_relat_1(sK3,sK0)),
% 1.28/0.53    inference(resolution,[],[f33,f59])).
% 1.28/0.53  fof(f59,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    inference(ennf_transformation,[],[f16])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.28/0.53    inference(pure_predicate_removal,[],[f9])).
% 1.28/0.53  fof(f9,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.28/0.53  fof(f69,plain,(
% 1.28/0.53    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.28/0.53    inference(subsumption_resolution,[],[f29,f31])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    v1_funct_1(sK3)),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f83,plain,(
% 1.28/0.53    ~r1_tarski(sK2,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 1.28/0.53    inference(resolution,[],[f78,f40])).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.28/0.53    inference(cnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.53  fof(f80,plain,(
% 1.28/0.53    k1_xboole_0 != k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.28/0.53    inference(resolution,[],[f79,f41])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f19])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f8])).
% 1.28/0.53  fof(f8,axiom,(
% 1.28/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.28/0.53  fof(f359,plain,(
% 1.28/0.53    sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.28/0.53    inference(subsumption_resolution,[],[f358,f43])).
% 1.28/0.53  fof(f358,plain,(
% 1.28/0.53    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.28/0.53    inference(forward_demodulation,[],[f282,f61])).
% 1.28/0.53  fof(f282,plain,(
% 1.28/0.53    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.28/0.53    inference(backward_demodulation,[],[f92,f269])).
% 1.28/0.53  fof(f92,plain,(
% 1.28/0.53    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.28/0.53    inference(resolution,[],[f77,f40])).
% 1.28/0.53  fof(f77,plain,(
% 1.28/0.53    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.28/0.53    inference(resolution,[],[f33,f46])).
% 1.28/0.53  fof(f46,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.28/0.53  fof(f337,plain,(
% 1.28/0.53    k1_xboole_0 = k1_relat_1(sK3)),
% 1.28/0.53    inference(forward_demodulation,[],[f336,f269])).
% 1.28/0.53  fof(f336,plain,(
% 1.28/0.53    sK0 = k1_relat_1(sK3)),
% 1.28/0.53    inference(subsumption_resolution,[],[f280,f43])).
% 1.28/0.53  fof(f280,plain,(
% 1.28/0.53    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.28/0.53    inference(backward_demodulation,[],[f89,f269])).
% 1.28/0.53  fof(f89,plain,(
% 1.28/0.53    ~r1_tarski(sK0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.28/0.53    inference(resolution,[],[f85,f40])).
% 1.28/0.53  fof(f413,plain,(
% 1.28/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2),
% 1.28/0.53    inference(forward_demodulation,[],[f294,f361])).
% 1.28/0.53  fof(f294,plain,(
% 1.28/0.53    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.28/0.53    inference(backward_demodulation,[],[f123,f269])).
% 1.28/0.53  fof(f372,plain,(
% 1.28/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 1.28/0.53    inference(backward_demodulation,[],[f334,f361])).
% 1.28/0.53  fof(f334,plain,(
% 1.28/0.53    ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.28/0.53    inference(subsumption_resolution,[],[f333,f331])).
% 1.28/0.53  fof(f331,plain,(
% 1.28/0.53    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.28/0.53    inference(forward_demodulation,[],[f271,f61])).
% 1.28/0.53  fof(f271,plain,(
% 1.28/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.28/0.53    inference(backward_demodulation,[],[f33,f269])).
% 1.28/0.53  fof(f333,plain,(
% 1.28/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.28/0.53    inference(forward_demodulation,[],[f332,f61])).
% 1.28/0.53  fof(f332,plain,(
% 1.28/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.28/0.53    inference(forward_demodulation,[],[f272,f269])).
% 1.28/0.53  fof(f272,plain,(
% 1.28/0.53    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.28/0.53    inference(backward_demodulation,[],[f69,f269])).
% 1.28/0.53  fof(f517,plain,(
% 1.28/0.53    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.28/0.53    inference(backward_demodulation,[],[f368,f512])).
% 1.28/0.53  fof(f512,plain,(
% 1.28/0.53    k1_xboole_0 = sK1),
% 1.28/0.53    inference(resolution,[],[f509,f418])).
% 1.28/0.53  fof(f509,plain,(
% 1.28/0.53    ( ! [X8] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X8) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f502,f507])).
% 1.28/0.53  fof(f507,plain,(
% 1.28/0.53    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(forward_demodulation,[],[f499,f374])).
% 1.28/0.53  fof(f499,plain,(
% 1.28/0.53    ( ! [X2,X3] : (k1_xboole_0 = sK1 | k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 1.28/0.53    inference(resolution,[],[f401,f56])).
% 1.28/0.53  fof(f401,plain,(
% 1.28/0.53    ( ! [X2,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(forward_demodulation,[],[f400,f361])).
% 1.28/0.53  fof(f400,plain,(
% 1.28/0.53    ( ! [X2,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f399,f43])).
% 1.28/0.53  fof(f399,plain,(
% 1.28/0.53    ( ! [X2,X1] : (~r1_tarski(k1_xboole_0,X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(forward_demodulation,[],[f398,f376])).
% 1.28/0.53  fof(f376,plain,(
% 1.28/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.28/0.53    inference(backward_demodulation,[],[f342,f361])).
% 1.28/0.53  fof(f342,plain,(
% 1.28/0.53    k1_xboole_0 = k2_relat_1(sK3)),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f338])).
% 1.28/0.53  fof(f338,plain,(
% 1.28/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK3)),
% 1.28/0.53    inference(backward_demodulation,[],[f81,f337])).
% 1.28/0.53  fof(f81,plain,(
% 1.28/0.53    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3)),
% 1.28/0.53    inference(resolution,[],[f79,f42])).
% 1.28/0.53  fof(f42,plain,(
% 1.28/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f19])).
% 1.28/0.53  fof(f398,plain,(
% 1.28/0.53    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(k1_xboole_0),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(forward_demodulation,[],[f397,f361])).
% 1.28/0.53  fof(f397,plain,(
% 1.28/0.53    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f287,f43])).
% 1.28/0.53  fof(f287,plain,(
% 1.28/0.53    ( ! [X2,X1] : (~r1_tarski(k1_xboole_0,X1) | ~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(backward_demodulation,[],[f104,f269])).
% 1.28/0.53  fof(f104,plain,(
% 1.28/0.53    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f102,f79])).
% 1.28/0.53  fof(f102,plain,(
% 1.28/0.53    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 1.28/0.53    inference(superposition,[],[f44,f97])).
% 1.28/0.53  fof(f502,plain,(
% 1.28/0.53    ( ! [X8] : (k1_xboole_0 = sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,X8,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X8)) )),
% 1.28/0.53    inference(resolution,[],[f401,f65])).
% 1.28/0.53  fof(f65,plain,(
% 1.28/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.28/0.53    inference(equality_resolution,[],[f52])).
% 1.28/0.53  fof(f52,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f25])).
% 1.28/0.53  fof(f368,plain,(
% 1.28/0.53    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 1.28/0.53    inference(backward_demodulation,[],[f270,f361])).
% 1.28/0.53  fof(f270,plain,(
% 1.28/0.53    v1_funct_2(sK3,k1_xboole_0,sK1)),
% 1.28/0.53    inference(backward_demodulation,[],[f32,f269])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (10405)------------------------------
% 1.28/0.53  % (10405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (10405)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (10405)Memory used [KB]: 6268
% 1.28/0.53  % (10405)Time elapsed: 0.098 s
% 1.28/0.53  % (10405)------------------------------
% 1.28/0.53  % (10405)------------------------------
% 1.28/0.54  % (10406)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.28/0.54  % (10393)Success in time 0.173 s
%------------------------------------------------------------------------------
