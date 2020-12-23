%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  147 (1038 expanded)
%              Number of leaves         :   18 ( 253 expanded)
%              Depth                    :   24
%              Number of atoms          :  431 (5981 expanded)
%              Number of equality atoms :  106 (1527 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(subsumption_resolution,[],[f332,f116])).

fof(f116,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f113,f52])).

fof(f52,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
      | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
        | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(superposition,[],[f104,f112])).

fof(f112,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f111,f83])).

fof(f83,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f82,f51])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f111,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f110,f90])).

fof(f90,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f73,f51])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f110,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f109,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f109,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f108,f50])).

fof(f50,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f108,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0) ),
    inference(resolution,[],[f107,f51])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v2_funct_2(sK2,X1)
      | ~ v3_funct_2(sK2,X0,X1) ) ),
    inference(resolution,[],[f76,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f104,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f103,f83])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f59,f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f332,plain,(
    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f331,f122])).

fof(f122,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f78,f51])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f331,plain,(
    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( sK1 != sK1
    | sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f151,f324])).

fof(f324,plain,(
    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f267,f52])).

fof(f267,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 ) ),
    inference(superposition,[],[f125,f264])).

fof(f264,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(superposition,[],[f263,f133])).

fof(f133,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f132,f112])).

fof(f132,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f131,f106])).

fof(f106,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f105,f86])).

fof(f86,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(resolution,[],[f54,f83])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f105,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) ),
    inference(resolution,[],[f104,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(resolution,[],[f130,f80])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f129,f83])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f128,f48])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f56,f102])).

fof(f102,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f101,f50])).

fof(f101,plain,
    ( v2_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0) ),
    inference(resolution,[],[f100,f51])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v2_funct_1(sK2)
      | ~ v3_funct_2(sK2,X0,X1) ) ),
    inference(resolution,[],[f75,f48])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(f263,plain,(
    sK0 = k9_relat_1(k2_funct_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f261,f221])).

fof(f221,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f220,f186])).

fof(f186,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f178,f82])).

fof(f178,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f177,f155])).

fof(f155,plain,(
    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f154,f48])).

fof(f154,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f153,f49])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f153,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f50])).

fof(f152,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f177,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f176,f48])).

fof(f176,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f175,f49])).

fof(f175,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f174,f50])).

fof(f174,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f68,f51])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f220,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f219,f184])).

fof(f184,plain,(
    v5_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f178,f73])).

fof(f219,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f191,f62])).

fof(f191,plain,(
    v2_funct_2(k2_funct_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f179,f173])).

fof(f173,plain,(
    v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(forward_demodulation,[],[f172,f155])).

fof(f172,plain,(
    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f171,f48])).

fof(f171,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f170,f49])).

fof(f170,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f169,f50])).

fof(f169,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f67,f51])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f179,plain,
    ( v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(resolution,[],[f178,f157])).

fof(f157,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_2(k2_funct_1(sK2),X2)
      | ~ v3_funct_2(k2_funct_1(sK2),X1,X2) ) ),
    inference(superposition,[],[f146,f155])).

fof(f146,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_2(k2_funct_2(sK0,sK2),X2)
      | ~ v3_funct_2(k2_funct_2(sK0,sK2),X1,X2) ) ),
    inference(resolution,[],[f144,f76])).

fof(f144,plain,(
    v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f143,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f142,f50])).

fof(f142,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(resolution,[],[f141,f51])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(sK2,X0,X0)
      | ~ v1_funct_2(sK2,X0,X0)
      | v1_funct_1(k2_funct_2(X0,sK2)) ) ),
    inference(resolution,[],[f65,f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f261,plain,(
    k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f208,f218])).

fof(f218,plain,(
    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f217,f186])).

fof(f217,plain,
    ( k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f185,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f185,plain,(
    v4_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f178,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f208,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(k2_funct_1(sK2),X1)) = k9_relat_1(k2_funct_1(sK2),X1) ),
    inference(resolution,[],[f186,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f124,f83])).

fof(f124,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f123,f48])).

fof(f123,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f60,f102])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f151,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f150,f121])).

fof(f121,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f77,f51])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f150,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f149,f121])).

fof(f149,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f53,f122])).

fof(f53,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:27:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (26165)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (26165)Refutation not found, incomplete strategy% (26165)------------------------------
% 0.20/0.46  % (26165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (26165)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (26165)Memory used [KB]: 6140
% 0.20/0.46  % (26165)Time elapsed: 0.043 s
% 0.20/0.46  % (26165)------------------------------
% 0.20/0.46  % (26165)------------------------------
% 0.20/0.46  % (26173)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.47  % (26173)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f333,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f332,f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.47    inference(resolution,[],[f113,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    r1_tarski(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    (sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f17])).
% 0.20/0.47  fof(f17,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.20/0.47    inference(superposition,[],[f104,f112])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    sK0 = k2_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f111,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f82,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.20/0.47    inference(resolution,[],[f55,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f110,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    v5_relat_1(sK2,sK0)),
% 0.20/0.47    inference(resolution,[],[f73,f51])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f109,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    v2_funct_2(sK2,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f108,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    v3_funct_2(sK2,sK0,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    v2_funct_2(sK2,sK0) | ~v3_funct_2(sK2,sK0,sK0)),
% 0.20/0.47    inference(resolution,[],[f107,f51])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_2(sK2,X1) | ~v3_funct_2(sK2,X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f76,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f103,f83])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(resolution,[],[f59,f48])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.47  fof(f332,plain,(
% 0.20/0.47    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.47    inference(superposition,[],[f331,f122])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK0,sK2,X0)) )),
% 0.20/0.47    inference(resolution,[],[f78,f51])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.47  fof(f331,plain,(
% 0.20/0.47    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f330])).
% 0.20/0.47  fof(f330,plain,(
% 0.20/0.47    sK1 != sK1 | sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.47    inference(superposition,[],[f151,f324])).
% 0.20/0.47  fof(f324,plain,(
% 0.20/0.47    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.47    inference(resolution,[],[f267,f52])).
% 0.20/0.47  fof(f267,plain,(
% 0.20/0.47    ( ! [X1] : (~r1_tarski(X1,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1) )),
% 0.20/0.47    inference(superposition,[],[f125,f264])).
% 0.20/0.47  fof(f264,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2)),
% 0.20/0.47    inference(superposition,[],[f263,f133])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.47    inference(forward_demodulation,[],[f132,f112])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.20/0.47    inference(forward_demodulation,[],[f131,f106])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.47    inference(forward_demodulation,[],[f105,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f54,f83])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2)))),
% 0.20/0.47    inference(resolution,[],[f104,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(flattening,[],[f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2)))),
% 0.20/0.47    inference(resolution,[],[f130,f80])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f129,f83])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f128,f48])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(resolution,[],[f56,f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    v2_funct_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f101,f50])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    v2_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0)),
% 0.20/0.47    inference(resolution,[],[f100,f51])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_1(sK2) | ~v3_funct_2(sK2,X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f75,f48])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f40])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 0.20/0.47  fof(f263,plain,(
% 0.20/0.47    sK0 = k9_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.47    inference(forward_demodulation,[],[f261,f221])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f220,f186])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    inference(resolution,[],[f178,f82])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    inference(forward_demodulation,[],[f177,f155])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    k2_funct_1(sK2) = k2_funct_2(sK0,sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f154,f48])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f153,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    v1_funct_2(sK2,sK0,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f152,f50])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f64,f51])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.47    inference(flattening,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    inference(subsumption_resolution,[],[f176,f48])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f175,f49])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f174,f50])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f68,f51])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.47    inference(flattening,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f219,f184])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    v5_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.47    inference(resolution,[],[f178,f73])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v5_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    inference(resolution,[],[f191,f62])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    v2_funct_2(k2_funct_1(sK2),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f179,f173])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 0.20/0.47    inference(forward_demodulation,[],[f172,f155])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f171,f48])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f170,f49])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f169,f50])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f67,f51])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    v2_funct_2(k2_funct_1(sK2),sK0) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 0.20/0.47    inference(resolution,[],[f178,f157])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_2(k2_funct_1(sK2),X2) | ~v3_funct_2(k2_funct_1(sK2),X1,X2)) )),
% 0.20/0.47    inference(superposition,[],[f146,f155])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_2(k2_funct_2(sK0,sK2),X2) | ~v3_funct_2(k2_funct_2(sK0,sK2),X1,X2)) )),
% 0.20/0.47    inference(resolution,[],[f144,f76])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f143,f49])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ~v1_funct_2(sK2,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f142,f50])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.20/0.47    inference(resolution,[],[f141,f51])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK2,X0,X0) | ~v1_funct_2(sK2,X0,X0) | v1_funct_1(k2_funct_2(X0,sK2))) )),
% 0.20/0.47    inference(resolution,[],[f65,f48])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f261,plain,(
% 0.20/0.47    k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    inference(superposition,[],[f208,f218])).
% 0.20/0.47  fof(f218,plain,(
% 0.20/0.47    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f217,f186])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    inference(resolution,[],[f185,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    v4_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.47    inference(resolution,[],[f178,f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    ( ! [X1] : (k2_relat_1(k7_relat_1(k2_funct_1(sK2),X1)) = k9_relat_1(k2_funct_1(sK2),X1)) )),
% 0.20/0.47    inference(resolution,[],[f186,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f124,f83])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f123,f48])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(resolution,[],[f60,f102])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.47    inference(forward_demodulation,[],[f150,f121])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) )),
% 0.20/0.47    inference(resolution,[],[f77,f51])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.47    inference(forward_demodulation,[],[f149,f121])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.47    inference(forward_demodulation,[],[f53,f122])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (26173)------------------------------
% 0.20/0.47  % (26173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (26173)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (26173)Memory used [KB]: 6396
% 0.20/0.47  % (26173)Time elapsed: 0.063 s
% 0.20/0.47  % (26173)------------------------------
% 0.20/0.47  % (26173)------------------------------
% 0.20/0.48  % (26151)Success in time 0.123 s
%------------------------------------------------------------------------------
