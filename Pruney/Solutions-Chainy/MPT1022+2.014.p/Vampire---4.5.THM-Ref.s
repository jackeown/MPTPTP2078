%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 602 expanded)
%              Number of leaves         :   14 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  261 (2605 expanded)
%              Number of equality atoms :   91 ( 726 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(subsumption_resolution,[],[f392,f314])).

fof(f314,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) ),
    inference(resolution,[],[f312,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f312,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f311,f100])).

fof(f100,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f95,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f311,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f310,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f310,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    inference(resolution,[],[f52,f207])).

fof(f207,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f203,f44])).

fof(f44,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f203,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f202,f45])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(sK2,X0,X1)
      | v2_funct_1(sK2) ) ),
    inference(resolution,[],[f73,f42])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f392,plain,(
    k1_xboole_0 != k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f298,f390])).

fof(f390,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f389,f362])).

fof(f362,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f361,f298])).

fof(f361,plain,
    ( sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f351,f46])).

fof(f46,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f351,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f312,f348])).

fof(f348,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f347,f178])).

fof(f178,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f64,f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f347,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f343,f43])).

fof(f43,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f343,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0) ),
    inference(resolution,[],[f72,f45])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f389,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f368,f47])).

fof(f368,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f115,f362])).

fof(f115,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f298,plain,(
    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f297,f292])).

fof(f292,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f76,f45])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f297,plain,(
    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f296,f267])).

fof(f267,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f261,f46])).

fof(f261,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f249,f259])).

fof(f259,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f258,f123])).

fof(f123,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f66,f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f258,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f257,f173])).

fof(f173,plain,(
    ! [X4] :
      ( ~ v2_funct_2(sK2,X4)
      | k2_relat_1(sK2) = X4
      | ~ v5_relat_1(sK2,X4) ) ),
    inference(resolution,[],[f55,f100])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f257,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f253,f44])).

fof(f253,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f252,f45])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(sK2,X0,X1)
      | v2_funct_2(sK2,X1) ) ),
    inference(resolution,[],[f74,f42])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f249,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f248,f100])).

fof(f248,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(resolution,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f296,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f275,f292])).

fof(f275,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f274,f270])).

fof(f270,plain,(
    ! [X0] : k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f75,f45])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f274,plain,
    ( sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f41,f270])).

fof(f41,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:02:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (13560)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (13567)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (13547)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (13567)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (13559)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (13561)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f394,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f392,f314])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0))),
% 0.20/0.50    inference(resolution,[],[f312,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f311,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f95,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.50    inference(negated_conjecture,[],[f18])).
% 0.20/0.50  fof(f18,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f48,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f310,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(sK2) | ~r1_tarski(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) )),
% 0.20/0.50    inference(resolution,[],[f52,f207])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f203,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    v3_funct_2(sK2,sK0,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ~v3_funct_2(sK2,sK0,sK0) | v2_funct_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f202,f45])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(sK2,X0,X1) | v2_funct_1(sK2)) )),
% 0.20/0.50    inference(resolution,[],[f73,f42])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.20/0.50  fof(f392,plain,(
% 0.20/0.50    k1_xboole_0 != k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0))),
% 0.20/0.50    inference(backward_demodulation,[],[f298,f390])).
% 0.20/0.50  fof(f390,plain,(
% 0.20/0.50    k1_xboole_0 = sK1),
% 0.20/0.50    inference(forward_demodulation,[],[f389,f362])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f361,f298])).
% 0.20/0.50  fof(f361,plain,(
% 0.20/0.50    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f351,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    r1_tarski(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f351,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(superposition,[],[f312,f348])).
% 0.20/0.50  fof(f348,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f347,f178])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)),
% 0.20/0.50    inference(resolution,[],[f64,f45])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f347,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK0,sK2) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f343,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f343,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0)),
% 0.20/0.50    inference(resolution,[],[f72,f45])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f389,plain,(
% 0.20/0.50    sK0 = sK1),
% 0.20/0.50    inference(subsumption_resolution,[],[f368,f47])).
% 0.20/0.50  fof(f368,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,sK1) | sK0 = sK1),
% 0.20/0.50    inference(backward_demodulation,[],[f115,f362])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.20/0.50    inference(resolution,[],[f58,f46])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.50    inference(superposition,[],[f297,f292])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) )),
% 0.20/0.50    inference(resolution,[],[f76,f45])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f296,f267])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.50    inference(resolution,[],[f261,f46])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.20/0.50    inference(backward_demodulation,[],[f249,f259])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    sK0 = k2_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f258,f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    v5_relat_1(sK2,sK0)),
% 0.20/0.50    inference(resolution,[],[f66,f45])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0)),
% 0.20/0.50    inference(resolution,[],[f257,f173])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    ( ! [X4] : (~v2_funct_2(sK2,X4) | k2_relat_1(sK2) = X4 | ~v5_relat_1(sK2,X4)) )),
% 0.20/0.50    inference(resolution,[],[f55,f100])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    v2_funct_2(sK2,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f253,f44])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    ~v3_funct_2(sK2,sK0,sK0) | v2_funct_2(sK2,sK0)),
% 0.20/0.50    inference(resolution,[],[f252,f45])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(sK2,X0,X1) | v2_funct_2(sK2,X1)) )),
% 0.20/0.50    inference(resolution,[],[f74,f42])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f248,f100])).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(sK2) | ~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.20/0.50    inference(resolution,[],[f51,f42])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f275,f292])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.50    inference(forward_demodulation,[],[f274,f270])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ( ! [X0] : (k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0)) )),
% 0.20/0.50    inference(resolution,[],[f75,f45])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f41,f270])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (13567)------------------------------
% 0.20/0.50  % (13567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13567)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (13567)Memory used [KB]: 1918
% 0.20/0.50  % (13567)Time elapsed: 0.075 s
% 0.20/0.50  % (13567)------------------------------
% 0.20/0.50  % (13567)------------------------------
% 0.20/0.50  % (13543)Success in time 0.138 s
%------------------------------------------------------------------------------
