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
% DateTime   : Thu Dec  3 13:06:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  151 (1116 expanded)
%              Number of leaves         :   18 ( 272 expanded)
%              Depth                    :   24
%              Number of atoms          :  446 (6427 expanded)
%              Number of equality atoms :  106 (1634 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(subsumption_resolution,[],[f420,f139])).

fof(f139,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f136,f55])).

fof(f55,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
      | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f45])).

fof(f45,plain,
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

fof(f136,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(superposition,[],[f126,f135])).

fof(f135,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f134,f88])).

fof(f88,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f58,f60])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f134,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f133,f100])).

fof(f100,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f78,f54])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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

fof(f133,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f132,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f132,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f131,f53])).

fof(f53,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f131,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0) ),
    inference(resolution,[],[f130,f54])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v2_funct_2(sK2,X1)
      | ~ v3_funct_2(sK2,X0,X1) ) ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f125,f88])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f65,f51])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f420,plain,(
    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f419,f148])).

fof(f148,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f83,f54])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f419,plain,(
    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) ),
    inference(trivial_inequality_removal,[],[f418])).

fof(f418,plain,
    ( sK1 != sK1
    | sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f200,f411])).

fof(f411,plain,(
    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f397,f55])).

fof(f397,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK0)
      | k10_relat_1(sK2,k9_relat_1(sK2,X2)) = X2 ) ),
    inference(superposition,[],[f157,f388])).

fof(f388,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(superposition,[],[f387,f171])).

fof(f171,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f170,f135])).

fof(f170,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f168,f109])).

fof(f109,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f102,f107])).

fof(f107,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f105,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f105,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),X3)
      | sK2 = k7_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f62,f88])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f102,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3) ),
    inference(resolution,[],[f61,f88])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f168,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(resolution,[],[f167,f85])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f166,f88])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f59,f124])).

fof(f124,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f123,f53])).

fof(f123,plain,
    ( v2_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0) ),
    inference(resolution,[],[f122,f54])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v2_funct_1(sK2)
      | ~ v3_funct_2(sK2,X0,X1) ) ),
    inference(resolution,[],[f80,f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(f387,plain,(
    sK0 = k9_relat_1(k2_funct_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f386,f273])).

fof(f273,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f272,f235])).

fof(f235,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f227,f87])).

% (11459)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f227,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f226,f204])).

fof(f204,plain,(
    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f203,f51])).

fof(f203,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f202,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f202,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f201,f53])).

fof(f201,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f69,f54])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f226,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f225,f51])).

fof(f225,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f224,f52])).

fof(f224,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f223,f53])).

fof(f223,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f73,f54])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
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
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f272,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f271,f233])).

fof(f233,plain,(
    v5_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f227,f78])).

fof(f271,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f240,f67])).

fof(f240,plain,(
    v2_funct_2(k2_funct_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f228,f222])).

fof(f222,plain,(
    v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(forward_demodulation,[],[f221,f204])).

fof(f221,plain,(
    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f220,f51])).

fof(f220,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f219,f52])).

fof(f219,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f218,f53])).

fof(f218,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f228,plain,
    ( v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(resolution,[],[f227,f206])).

fof(f206,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_2(k2_funct_1(sK2),X2)
      | ~ v3_funct_2(k2_funct_1(sK2),X1,X2) ) ),
    inference(superposition,[],[f195,f204])).

fof(f195,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_2(k2_funct_2(sK0,sK2),X2)
      | ~ v3_funct_2(k2_funct_2(sK0,sK2),X1,X2) ) ),
    inference(resolution,[],[f193,f81])).

fof(f193,plain,(
    v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f192,f52])).

fof(f192,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f191,f53])).

fof(f191,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(resolution,[],[f190,f54])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(sK2,X0,X0)
      | ~ v1_funct_2(sK2,X0,X0)
      | v1_funct_1(k2_funct_2(X0,sK2)) ) ),
    inference(resolution,[],[f70,f51])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f386,plain,(
    k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f259,f384])).

fof(f384,plain,(
    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f381,f234])).

fof(f234,plain,(
    v4_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f227,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f381,plain,(
    ! [X0] :
      ( ~ v4_relat_1(k2_funct_1(sK2),X0)
      | k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f379,f235])).

fof(f379,plain,(
    ! [X0] :
      ( k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),X0)
      | ~ v4_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f258,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f258,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),X2)
      | k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),X2) ) ),
    inference(resolution,[],[f235,f62])).

fof(f259,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(k2_funct_1(sK2),X3)) = k9_relat_1(k2_funct_1(sK2),X3) ),
    inference(resolution,[],[f235,f61])).

fof(f157,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f156,f88])).

fof(f156,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f155,f51])).

fof(f155,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f66,f124])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f200,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f199,f147])).

fof(f147,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f82,f54])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f199,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f198,f147])).

fof(f198,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f56,f148])).

fof(f56,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.48  % (11477)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (11477)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f421,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f420,f139])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.22/0.50    inference(resolution,[],[f136,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    r1_tarski(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    (sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f18])).
% 0.22/0.50  fof(f18,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.22/0.50    inference(superposition,[],[f126,f135])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    sK0 = k2_relat_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f134,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f87,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f46])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f58,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f133,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    v5_relat_1(sK2,sK0)),
% 0.22/0.50    inference(resolution,[],[f78,f54])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f132,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    v2_funct_2(sK2,sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f131,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    v3_funct_2(sK2,sK0,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f46])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    v2_funct_2(sK2,sK0) | ~v3_funct_2(sK2,sK0,sK0)),
% 0.22/0.50    inference(resolution,[],[f130,f54])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_2(sK2,X1) | ~v3_funct_2(sK2,X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f81,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f46])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f125,f88])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f65,f51])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.22/0.50    inference(superposition,[],[f419,f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK0,sK2,X0)) )),
% 0.22/0.50    inference(resolution,[],[f83,f54])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f418])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    sK1 != sK1 | sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))),
% 0.22/0.50    inference(superposition,[],[f200,f411])).
% 0.22/0.50  fof(f411,plain,(
% 0.22/0.50    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.22/0.50    inference(resolution,[],[f397,f55])).
% 0.22/0.50  fof(f397,plain,(
% 0.22/0.50    ( ! [X2] : (~r1_tarski(X2,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X2)) = X2) )),
% 0.22/0.50    inference(superposition,[],[f157,f388])).
% 0.22/0.50  fof(f388,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK2)),
% 0.22/0.50    inference(superposition,[],[f387,f171])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f170,f135])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.22/0.50    inference(forward_demodulation,[],[f168,f109])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.50    inference(superposition,[],[f102,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f105,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(flattening,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),X3) | sK2 = k7_relat_1(sK2,X3)) )),
% 0.22/0.50    inference(resolution,[],[f62,f88])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X3] : (k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)) )),
% 0.22/0.50    inference(resolution,[],[f61,f88])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2)))),
% 0.22/0.50    inference(resolution,[],[f167,f85])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f166,f88])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f165,f51])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f59,f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    v2_funct_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f53])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0)),
% 0.22/0.50    inference(resolution,[],[f122,f54])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_1(sK2) | ~v3_funct_2(sK2,X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f80,f51])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f42])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 0.22/0.50  fof(f387,plain,(
% 0.22/0.50    sK0 = k9_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f386,f273])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f272,f235])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f227,f87])).
% 0.22/0.51  % (11459)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f226,f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_funct_2(sK0,sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f203,f51])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f202,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f201,f53])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(resolution,[],[f69,f54])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f225,f51])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f224,f52])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f223,f53])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(resolution,[],[f73,f54])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f271,f233])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    v5_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.51    inference(resolution,[],[f227,f78])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v5_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    inference(resolution,[],[f240,f67])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    v2_funct_2(k2_funct_1(sK2),sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f228,f222])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 0.22/0.51    inference(forward_demodulation,[],[f221,f204])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f220,f51])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f219,f52])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f218,f53])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(resolution,[],[f72,f54])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    v2_funct_2(k2_funct_1(sK2),sK0) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 0.22/0.51    inference(resolution,[],[f227,f206])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_2(k2_funct_1(sK2),X2) | ~v3_funct_2(k2_funct_1(sK2),X1,X2)) )),
% 0.22/0.51    inference(superposition,[],[f195,f204])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_2(k2_funct_2(sK0,sK2),X2) | ~v3_funct_2(k2_funct_2(sK0,sK2),X1,X2)) )),
% 0.22/0.51    inference(resolution,[],[f193,f81])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f192,f52])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ~v1_funct_2(sK2,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f191,f53])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f190,f54])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK2,X0,X0) | ~v1_funct_2(sK2,X0,X0) | v1_funct_1(k2_funct_2(X0,sK2))) )),
% 0.22/0.51    inference(resolution,[],[f70,f51])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f386,plain,(
% 0.22/0.51    k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    inference(superposition,[],[f259,f384])).
% 0.22/0.51  fof(f384,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.51    inference(resolution,[],[f381,f234])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    v4_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.51    inference(resolution,[],[f227,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f381,plain,(
% 0.22/0.51    ( ! [X0] : (~v4_relat_1(k2_funct_1(sK2),X0) | k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f379,f235])).
% 0.22/0.51  fof(f379,plain,(
% 0.22/0.51    ( ! [X0] : (k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),X0) | ~v4_relat_1(k2_funct_1(sK2),X0) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.22/0.51    inference(resolution,[],[f258,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    ( ! [X2] : (~r1_tarski(k1_relat_1(k2_funct_1(sK2)),X2) | k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),X2)) )),
% 0.22/0.51    inference(resolution,[],[f235,f62])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    ( ! [X3] : (k2_relat_1(k7_relat_1(k2_funct_1(sK2),X3)) = k9_relat_1(k2_funct_1(sK2),X3)) )),
% 0.22/0.51    inference(resolution,[],[f235,f61])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f156,f88])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f155,f51])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.51    inference(resolution,[],[f66,f124])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f199,f147])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) )),
% 0.22/0.51    inference(resolution,[],[f82,f54])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f198,f147])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f56,f148])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (11477)------------------------------
% 0.22/0.51  % (11477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11477)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (11477)Memory used [KB]: 6396
% 0.22/0.51  % (11477)Time elapsed: 0.024 s
% 0.22/0.51  % (11477)------------------------------
% 0.22/0.51  % (11477)------------------------------
% 0.22/0.52  % (11453)Success in time 0.146 s
%------------------------------------------------------------------------------
