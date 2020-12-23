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
% DateTime   : Thu Dec  3 13:06:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 (1518 expanded)
%              Number of leaves         :   16 ( 373 expanded)
%              Depth                    :   28
%              Number of atoms          :  345 (7866 expanded)
%              Number of equality atoms :  104 (2004 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(subsumption_resolution,[],[f282,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f282,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f235,f269])).

fof(f269,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f268,f49])).

fof(f268,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f251,f239])).

fof(f239,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f237,f47])).

fof(f47,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2))
      | sK2 != k7_relset_1(sK1,sK1,sK3,k8_relset_1(sK1,sK1,sK3,sK2)) )
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK3,sK1,sK1)
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2))
        | sK2 != k7_relset_1(sK1,sK1,sK3,k8_relset_1(sK1,sK1,sK3,sK2)) )
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK3,sK1,sK1)
      & v1_funct_2(sK3,sK1,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(f237,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f235,f195])).

fof(f195,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f194,f117])).

fof(f117,plain,(
    sK1 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f116,f94])).

fof(f94,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f89,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f89,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f116,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f115,f88])).

fof(f88,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f115,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f111,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f111,plain,(
    v2_funct_2(sK3,sK1) ),
    inference(resolution,[],[f93,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f93,plain,(
    sP0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f92,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,
    ( sP0(sK1,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f87,f45])).

fof(f45,plain,(
    v3_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,
    ( sP0(sK1,sK3)
    | ~ v3_funct_2(sK3,sK1,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f46,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP0(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f29,f34])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f194,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f193,f168])).

fof(f168,plain,
    ( v5_relat_1(sK3,k1_xboole_0)
    | sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f159,f130])).

fof(f130,plain,(
    k1_relat_1(sK3) = k10_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f125,f94])).

fof(f125,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f50,f117])).

fof(f50,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f159,plain,
    ( v5_relat_1(sK3,k1_xboole_0)
    | sK1 = k10_relat_1(sK3,sK1) ),
    inference(superposition,[],[f88,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k10_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f149,f43])).

fof(f149,plain,
    ( sK1 = k10_relat_1(sK3,sK1)
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f148,f44])).

fof(f44,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f148,plain,
    ( sK1 = k10_relat_1(sK3,sK1)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK1,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f146,f46])).

fof(f146,plain,
    ( sK1 = k10_relat_1(sK3,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_2(sK3,sK1,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f84,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f84,plain,(
    ! [X0] : k8_relset_1(sK1,sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f193,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f191,f94])).

fof(f191,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f170,f55])).

fof(f170,plain,
    ( v2_funct_2(sK3,k1_xboole_0)
    | sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f161,f130])).

fof(f161,plain,
    ( v2_funct_2(sK3,k1_xboole_0)
    | sK1 = k10_relat_1(sK3,sK1) ),
    inference(superposition,[],[f111,f150])).

fof(f251,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f78,f239])).

fof(f78,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f47,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f235,plain,(
    ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f234,f94])).

fof(f234,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f233,f43])).

fof(f233,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f232,f110])).

fof(f110,plain,(
    v2_funct_1(sK3) ),
    inference(resolution,[],[f93,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f232,plain,
    ( ~ v2_funct_1(sK3)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f231])).

fof(f231,plain,
    ( sK2 != sK2
    | ~ v2_funct_1(sK3)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f229,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f229,plain,(
    sK2 != k10_relat_1(sK3,k9_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f228,f47])).

fof(f228,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK2 != k10_relat_1(sK3,k9_relat_1(sK3,sK2)) ),
    inference(forward_demodulation,[],[f227,f117])).

fof(f227,plain,
    ( sK2 != k10_relat_1(sK3,k9_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f226,f84])).

fof(f226,plain,
    ( sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f225,f94])).

fof(f225,plain,
    ( sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f221,f43])).

fof(f221,plain,
    ( sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,
    ( sK2 != sK2
    | sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f203,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f203,plain,
    ( sK2 != k9_relat_1(sK3,k10_relat_1(sK3,sK2))
    | sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2)) ),
    inference(forward_demodulation,[],[f201,f85])).

fof(f85,plain,(
    ! [X1] : k7_relset_1(sK1,sK1,sK3,X1) = k9_relat_1(sK3,X1) ),
    inference(resolution,[],[f46,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f201,plain,
    ( sK2 != k9_relat_1(sK3,k10_relat_1(sK3,sK2))
    | sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2)) ),
    inference(backward_demodulation,[],[f145,f85])).

fof(f145,plain,
    ( sK2 != k7_relset_1(sK1,sK1,sK3,k10_relat_1(sK3,sK2))
    | sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2)) ),
    inference(backward_demodulation,[],[f48,f84])).

fof(f48,plain,
    ( sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2))
    | sK2 != k7_relset_1(sK1,sK1,sK3,k8_relset_1(sK1,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (11544)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (11544)Refutation not found, incomplete strategy% (11544)------------------------------
% 0.21/0.52  % (11544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11544)Memory used [KB]: 10618
% 0.21/0.52  % (11544)Time elapsed: 0.085 s
% 0.21/0.52  % (11544)------------------------------
% 0.21/0.52  % (11544)------------------------------
% 0.21/0.53  % (11553)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (11553)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f282,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3))),
% 0.21/0.53    inference(backward_demodulation,[],[f235,f269])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    k1_xboole_0 = sK2),
% 0.21/0.53    inference(subsumption_resolution,[],[f268,f49])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 0.21/0.53    inference(forward_demodulation,[],[f251,f239])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(subsumption_resolution,[],[f237,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    r1_tarski(sK2,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    (sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2)) | sK2 != k7_relset_1(sK1,sK1,sK3,k8_relset_1(sK1,sK1,sK3,sK2))) & r1_tarski(sK2,sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2)) | sK2 != k7_relset_1(sK1,sK1,sK3,k8_relset_1(sK1,sK1,sK3,sK2))) & r1_tarski(sK2,sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    ~r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(superposition,[],[f235,f195])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(forward_demodulation,[],[f194,f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    sK1 = k2_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f116,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    v1_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f89,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK1))),
% 0.21/0.53    inference(resolution,[],[f46,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    sK1 = k2_relat_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f115,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    v5_relat_1(sK3,sK1)),
% 0.21/0.53    inference(resolution,[],[f46,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    sK1 = k2_relat_1(sK3) | ~v5_relat_1(sK3,sK1) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f111,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    v2_funct_2(sK3,sK1)),
% 0.21/0.53    inference(resolution,[],[f93,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_funct_2(X1,X0) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP0(X1,X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP0(X1,X2))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    sP0(sK1,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f92,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    sP0(sK1,sK3) | ~v1_funct_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f87,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    v3_funct_2(sK3,sK1,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    sP0(sK1,sK3) | ~v3_funct_2(sK3,sK1,sK1) | ~v1_funct_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f46,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (sP0(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(definition_folding,[],[f29,f34])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    sK1 = k1_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f193,f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    v5_relat_1(sK3,k1_xboole_0) | sK1 = k1_relat_1(sK3)),
% 0.21/0.53    inference(forward_demodulation,[],[f159,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    k1_relat_1(sK3) = k10_relat_1(sK3,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f94])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    k1_relat_1(sK3) = k10_relat_1(sK3,sK1) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(superposition,[],[f50,f117])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    v5_relat_1(sK3,k1_xboole_0) | sK1 = k10_relat_1(sK3,sK1)),
% 0.21/0.53    inference(superposition,[],[f88,f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | sK1 = k10_relat_1(sK3,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f149,f43])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    sK1 = k10_relat_1(sK3,sK1) | k1_xboole_0 = sK1 | ~v1_funct_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f148,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK1,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    sK1 = k10_relat_1(sK3,sK1) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK1,sK1) | ~v1_funct_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f46])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    sK1 = k10_relat_1(sK3,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_2(sK3,sK1,sK1) | ~v1_funct_1(sK3)),
% 0.21/0.53    inference(superposition,[],[f84,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (k8_relset_1(sK1,sK1,sK3,X0) = k10_relat_1(sK3,X0)) )),
% 0.21/0.53    inference(resolution,[],[f46,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    sK1 = k1_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3) | ~v5_relat_1(sK3,k1_xboole_0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f191,f94])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    sK1 = k1_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3) | ~v5_relat_1(sK3,k1_xboole_0) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f170,f55])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    v2_funct_2(sK3,k1_xboole_0) | sK1 = k1_relat_1(sK3)),
% 0.21/0.53    inference(forward_demodulation,[],[f161,f130])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    v2_funct_2(sK3,k1_xboole_0) | sK1 = k10_relat_1(sK3,sK1)),
% 0.21/0.53    inference(superposition,[],[f111,f150])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f78,f239])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    sK1 = sK2 | ~r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f47,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    ~r1_tarski(sK2,k1_relat_1(sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f234,f94])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f233,f43])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f232,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    v2_funct_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f93,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_funct_1(X1) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ~v2_funct_1(sK3) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f231])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    sK2 != sK2 | ~v2_funct_1(sK3) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(superposition,[],[f229,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    sK2 != k10_relat_1(sK3,k9_relat_1(sK3,sK2))),
% 0.21/0.54    inference(subsumption_resolution,[],[f228,f47])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    ~r1_tarski(sK2,sK1) | sK2 != k10_relat_1(sK3,k9_relat_1(sK3,sK2))),
% 0.21/0.54    inference(forward_demodulation,[],[f227,f117])).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    sK2 != k10_relat_1(sK3,k9_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.54    inference(forward_demodulation,[],[f226,f84])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f225,f94])).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f221,f43])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f220])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    sK2 != sK2 | sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(superposition,[],[f203,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    sK2 != k9_relat_1(sK3,k10_relat_1(sK3,sK2)) | sK2 != k8_relset_1(sK1,sK1,sK3,k9_relat_1(sK3,sK2))),
% 0.21/0.54    inference(forward_demodulation,[],[f201,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X1] : (k7_relset_1(sK1,sK1,sK3,X1) = k9_relat_1(sK3,X1)) )),
% 0.21/0.54    inference(resolution,[],[f46,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    sK2 != k9_relat_1(sK3,k10_relat_1(sK3,sK2)) | sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2))),
% 0.21/0.54    inference(backward_demodulation,[],[f145,f85])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    sK2 != k7_relset_1(sK1,sK1,sK3,k10_relat_1(sK3,sK2)) | sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2))),
% 0.21/0.54    inference(backward_demodulation,[],[f48,f84])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    sK2 != k8_relset_1(sK1,sK1,sK3,k7_relset_1(sK1,sK1,sK3,sK2)) | sK2 != k7_relset_1(sK1,sK1,sK3,k8_relset_1(sK1,sK1,sK3,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (11553)------------------------------
% 0.21/0.54  % (11553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11553)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (11553)Memory used [KB]: 1663
% 0.21/0.54  % (11553)Time elapsed: 0.107 s
% 0.21/0.54  % (11553)------------------------------
% 0.21/0.54  % (11553)------------------------------
% 0.21/0.54  % (11543)Success in time 0.18 s
%------------------------------------------------------------------------------
