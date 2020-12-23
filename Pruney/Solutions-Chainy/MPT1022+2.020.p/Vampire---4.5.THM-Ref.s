%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 668 expanded)
%              Number of leaves         :   14 ( 163 expanded)
%              Depth                    :   22
%              Number of atoms          :  373 (3931 expanded)
%              Number of equality atoms :   82 (1010 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(subsumption_resolution,[],[f372,f328])).

fof(f328,plain,(
    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f322,f132])).

fof(f132,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
      | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f35])).

fof(f35,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(f322,plain,(
    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(trivial_inequality_removal,[],[f321])).

fof(f321,plain,
    ( sK1 != sK1
    | sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f157,f320])).

fof(f320,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f203,f42])).

fof(f42,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f203,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f196,f158])).

fof(f158,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f138,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f138,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f41,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f196,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f67,f195])).

fof(f195,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f194,f158])).

fof(f194,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f193,f137])).

fof(f137,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f193,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f126,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f126,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f106,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f40,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f40,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f157,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f156,f133])).

fof(f133,plain,(
    ! [X1] : k9_relat_1(sK2,X1) = k7_relset_1(sK0,sK0,sK2,X1) ),
    inference(resolution,[],[f41,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f156,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f155,f133])).

fof(f155,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f43,f132])).

fof(f43,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f372,plain,(
    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f370,f42])).

fof(f370,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f369,f158])).

fof(f369,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f360,f124])).

fof(f124,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f123,f41])).

fof(f123,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f105,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f40,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f360,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | ~ v2_funct_1(sK2)
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1
      | ~ v1_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f68,f359])).

fof(f359,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f167,f358])).

fof(f358,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f357,f297])).

fof(f297,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f280,f47])).

fof(f280,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f92,f95])).

fof(f95,plain,(
    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f94,f38])).

fof(f94,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f93,f40])).

fof(f93,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f80,f41])).

fof(f80,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f91,f38])).

fof(f91,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f90,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f79,f41])).

fof(f79,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f39,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

% (31964)Refutation not found, incomplete strategy% (31964)------------------------------
% (31964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31964)Termination reason: Refutation not found, incomplete strategy

% (31964)Memory used [KB]: 10618
% (31964)Time elapsed: 0.073 s
% (31964)------------------------------
% (31964)------------------------------
% (31960)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f357,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f356,f279])).

fof(f279,plain,(
    v5_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f96,f58])).

fof(f356,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f234,f50])).

fof(f234,plain,(
    v2_funct_2(k2_funct_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f233,f96])).

fof(f233,plain,
    ( v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f211,f99])).

fof(f99,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f83,f95])).

fof(f83,plain,(
    v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f82,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f81,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f76,f41])).

fof(f76,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f39,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f211,plain,
    ( v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f97,f61])).

fof(f97,plain,(
    v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(backward_demodulation,[],[f89,f95])).

fof(f89,plain,(
    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f88,f38])).

fof(f88,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f78,f41])).

fof(f78,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f39,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f167,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f166,f158])).

fof(f166,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f161,f38])).

fof(f161,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f124,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f68,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK2))
      | ~ v2_funct_1(sK2)
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (31948)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (31957)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (31961)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (31949)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (31946)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (31953)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (31954)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (31947)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (31954)Refutation not found, incomplete strategy% (31954)------------------------------
% 0.21/0.47  % (31954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31954)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (31954)Memory used [KB]: 6140
% 0.21/0.47  % (31954)Time elapsed: 0.065 s
% 0.21/0.47  % (31954)------------------------------
% 0.21/0.47  % (31954)------------------------------
% 0.21/0.47  % (31964)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31948)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f372,f328])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.21/0.48    inference(superposition,[],[f322,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) )),
% 0.21/0.48    inference(resolution,[],[f41,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    (sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f321])).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    sK1 != sK1 | sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.21/0.48    inference(backward_demodulation,[],[f157,f320])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.21/0.48    inference(resolution,[],[f203,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f196,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.21/0.48    inference(resolution,[],[f41,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f67,f195])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    sK0 = k2_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f194,f158])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f193,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    v5_relat_1(sK2,sK0)),
% 0.21/0.48    inference(resolution,[],[f41,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f126,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    v2_funct_2(sK2,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f125,f41])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    v2_funct_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    v2_funct_2(sK2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(resolution,[],[f40,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f38,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.21/0.48    inference(forward_demodulation,[],[f156,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X1] : (k9_relat_1(sK2,X1) = k7_relset_1(sK0,sK0,sK2,X1)) )),
% 0.21/0.48    inference(resolution,[],[f41,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.48    inference(backward_demodulation,[],[f155,f133])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.48    inference(backward_demodulation,[],[f43,f132])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.21/0.48    inference(resolution,[],[f370,f42])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f369,f158])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f360,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    v2_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f41])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f38])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(resolution,[],[f40,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,sK0) | ~v2_funct_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f68,f359])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f167,f358])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f357,f297])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f280,f47])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.21/0.48    inference(resolution,[],[f96,f44])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(backward_demodulation,[],[f92,f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k2_funct_2(sK0,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f38])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f40])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f41])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f39,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f38])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f40])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f41])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f39,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  % (31964)Refutation not found, incomplete strategy% (31964)------------------------------
% 0.21/0.48  % (31964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31964)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31964)Memory used [KB]: 10618
% 0.21/0.48  % (31964)Time elapsed: 0.073 s
% 0.21/0.48  % (31964)------------------------------
% 0.21/0.48  % (31964)------------------------------
% 0.21/0.48  % (31960)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f356,f279])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    v5_relat_1(k2_funct_1(sK2),sK0)),
% 0.21/0.48    inference(resolution,[],[f96,f58])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v5_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    inference(resolution,[],[f234,f50])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    v2_funct_2(k2_funct_1(sK2),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f233,f96])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    v2_funct_2(k2_funct_1(sK2),sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f211,f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.48    inference(backward_demodulation,[],[f83,f95])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f82,f38])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_2(sK0,sK2)) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f40])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_2(sK0,sK2)) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f41])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_2(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f39,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    v2_funct_2(k2_funct_1(sK2),sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(resolution,[],[f97,f61])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f89,f95])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f38])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f40])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f41])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f39,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f166,f158])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f161,f38])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f124,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f38,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31948)------------------------------
% 0.21/0.48  % (31948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31948)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31948)Memory used [KB]: 1791
% 0.21/0.48  % (31948)Time elapsed: 0.072 s
% 0.21/0.48  % (31948)------------------------------
% 0.21/0.48  % (31948)------------------------------
% 0.21/0.48  % (31943)Success in time 0.119 s
%------------------------------------------------------------------------------
