%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  160 (3384 expanded)
%              Number of leaves         :   21 (1016 expanded)
%              Depth                    :   33
%              Number of atoms          :  608 (27626 expanded)
%              Number of equality atoms :  188 (1378 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f387,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f103,f376,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f376,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f351,f317])).

fof(f317,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f316,f99])).

fof(f99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f89,f87])).

fof(f87,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f59,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f89,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f316,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f315,f107])).

fof(f107,plain,(
    k1_xboole_0 = k8_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f105,f101])).

fof(f101,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f90,f87])).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f60])).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f105,plain,(
    k1_xboole_0 = k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f67,f99])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f315,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f300,f116])).

fof(f116,plain,(
    ! [X0] :
      ( k8_relat_1(k1_xboole_0,X0) = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f93,f87])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f71,f60])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f300,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f299,f102])).

fof(f102,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f91,f87])).

fof(f91,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f299,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f298,f259])).

fof(f259,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f230,f212])).

fof(f212,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f56,f206])).

fof(f206,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f205,f56])).

fof(f205,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f199,f96])).

fof(f199,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f151,f197])).

fof(f197,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f196,f53])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f196,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f195,f54])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f195,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f194,f56])).

fof(f194,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(sK1) ),
    inference(resolution,[],[f183,f57])).

fof(f57,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | k2_funct_1(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f182,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

% (23592)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f182,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | k2_funct_1(sK1) = X0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(subsumption_resolution,[],[f181,f155])).

fof(f155,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f154,f51])).

fof(f51,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f154,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f144,f52])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v3_funct_2(sK1,X0,sK0)
      | sK0 = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f143,plain,(
    ! [X0] :
      ( sK0 = k2_relat_1(sK1)
      | ~ v3_funct_2(sK1,X0,sK0)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(resolution,[],[f135,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f135,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f126,f52])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k2_relat_1(X0) = X1
      | ~ v2_funct_2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f125,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_2(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(resolution,[],[f72,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f181,plain,(
    ! [X0] :
      ( sK0 != k2_relat_1(sK1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | k2_funct_1(sK1) = X0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(superposition,[],[f173,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f173,plain,(
    ! [X0] :
      ( sK0 != k2_relset_1(sK0,sK0,sK1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | k2_funct_1(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f172,f50])).

fof(f50,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f172,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | sK0 != k2_relset_1(sK0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | k2_funct_1(sK1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | sK0 != k2_relset_1(sK0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = sK0
      | ~ v1_funct_2(sK1,sK0,sK0)
      | k2_funct_1(sK1) = X0 ) ),
    inference(resolution,[],[f161,f52])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK1,X2),k6_partfun1(X1))
      | k2_relset_1(X1,X0,sK1) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK1,X1,X0)
      | k2_funct_1(sK1) = X2 ) ),
    inference(resolution,[],[f97,f49])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k2_funct_1(X2) = X3 ) ),
    inference(subsumption_resolution,[],[f84,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f151,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f150,f49])).

fof(f150,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f149,f50])).

fof(f149,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f148,f51])).

fof(f148,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f147,f52])).

fof(f147,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f58,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
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
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f58,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

% (23588)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(trivial_inequality_removal,[],[f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f165,f206])).

fof(f165,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK0
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f115,f164])).

fof(f164,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f163,f55])).

fof(f55,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f163,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | sK0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f146,f56])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v3_funct_2(sK2,X0,sK0)
      | sK0 = k2_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f145,f53])).

fof(f145,plain,(
    ! [X0] :
      ( sK0 = k2_relat_1(sK2)
      | ~ v3_funct_2(sK2,X0,sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(resolution,[],[f136,f81])).

fof(f136,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | sK0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f126,f56])).

fof(f115,plain,(
    ! [X2,X3,X1] :
      ( k1_xboole_0 != k2_relat_1(X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f69,f75])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f298,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f297,f259])).

fof(f297,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f266,f260])).

fof(f260,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f53,f259])).

fof(f266,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f192,f259])).

fof(f192,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)
    | sK2 = k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f191,f101])).

fof(f191,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)
    | sK2 = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f190,f87])).

fof(f190,plain,
    ( k6_partfun1(k1_xboole_0) != k5_relat_1(k1_xboole_0,sK2)
    | sK2 = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f189,f99])).

fof(f189,plain,
    ( k6_partfun1(k1_xboole_0) != k5_relat_1(k1_xboole_0,sK2)
    | sK2 = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f185,f100])).

fof(f100,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f88,f87])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f60])).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f185,plain,
    ( k6_partfun1(k1_xboole_0) != k5_relat_1(k1_xboole_0,sK2)
    | sK2 = k2_funct_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_relat_1(sK2) ),
    inference(superposition,[],[f180,f102])).

fof(f180,plain,(
    ! [X0] :
      ( k6_partfun1(k1_relat_1(X0)) != k5_relat_1(X0,sK2)
      | k2_funct_1(X0) = sK2
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_relat_1(sK2) ) ),
    inference(resolution,[],[f169,f56])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | k6_partfun1(k1_relat_1(X0)) != k5_relat_1(X0,sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_relat_1(sK2) ) ),
    inference(resolution,[],[f153,f75])).

fof(f153,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK2)
      | k2_relat_1(X1) != k1_relat_1(sK2)
      | ~ v2_funct_1(X1)
      | k2_funct_1(X1) = sK2
      | k5_relat_1(X1,sK2) != k6_partfun1(k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f92,f53])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f70,f60])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f351,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f271,f338])).

fof(f338,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f231,f209])).

fof(f209,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f52,f206])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK1 ) ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f156,f206])).

fof(f156,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK0
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f115,f155])).

fof(f271,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f216,f259])).

fof(f216,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f151,f206])).

% (23589)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f103,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f64,f87])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (23607)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (23599)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (23599)Refutation not found, incomplete strategy% (23599)------------------------------
% 0.21/0.51  % (23599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23599)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23599)Memory used [KB]: 1791
% 0.21/0.51  % (23599)Time elapsed: 0.047 s
% 0.21/0.51  % (23599)------------------------------
% 0.21/0.51  % (23599)------------------------------
% 0.21/0.51  % (23604)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (23598)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (23607)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f387,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f103,f376,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f351,f317])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f316,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    v1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f89,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.52    inference(definition_unfolding,[],[f59,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f61,f60])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f315,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    k1_xboole_0 = k8_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f105,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f90,f87])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f66,f60])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    k1_xboole_0 = k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f67,f99])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 0.21/0.52  fof(f315,plain,(
% 0.21/0.52    k1_xboole_0 != k8_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f300,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ( ! [X0] : (k8_relat_1(k1_xboole_0,X0) = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(superposition,[],[f93,f87])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f71,f60])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.52  fof(f300,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f299,f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f91,f87])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f65,f60])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f298,f259])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    k1_xboole_0 = sK2),
% 0.21/0.52    inference(resolution,[],[f230,f212])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.52    inference(backward_demodulation,[],[f56,f206])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f205,f56])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(resolution,[],[f199,f96])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(superposition,[],[f151,f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f196,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f45,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f19])).
% 0.21/0.52  fof(f19,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | sK2 = k2_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f195,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f194,f56])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f183,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | k2_funct_1(sK1) = X0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f182,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  % (23592)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | k2_funct_1(sK1) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f181,f155])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f154,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ~v3_funct_2(sK1,sK0,sK0) | sK0 = k2_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f144,f52])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v3_funct_2(sK1,X0,sK0) | sK0 = k2_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f143,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 = k2_relat_1(sK1) | ~v3_funct_2(sK1,X0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 0.21/0.52    inference(resolution,[],[f135,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~v2_funct_2(sK1,sK0) | sK0 = k2_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f126,f52])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k2_relat_1(X0) = X1 | ~v2_funct_2(X0,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_funct_2(X0,X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.52    inference(resolution,[],[f72,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | ~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 != k2_relat_1(sK1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | k2_funct_1(sK1) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) )),
% 0.21/0.52    inference(superposition,[],[f173,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 != k2_relset_1(sK0,sK0,sK1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k1_xboole_0 = sK0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | k2_funct_1(sK1) = X0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f172,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(sK1,sK0,sK0) | k2_funct_1(sK1) = X0) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f171])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | k2_funct_1(sK1) = X0) )),
% 0.21/0.52    inference(resolution,[],[f161,f52])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK1,X2),k6_partfun1(X1)) | k2_relset_1(X1,X0,sK1) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK1,X1,X0) | k2_funct_1(sK1) = X2) )),
% 0.21/0.52    inference(resolution,[],[f97,f49])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k2_funct_1(X2) = X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f150,f49])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f149,f50])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f148,f51])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f147,f52])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(superposition,[],[f58,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  % (23588)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f222])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f165,f206])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(superposition,[],[f115,f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~v3_funct_2(sK2,sK0,sK0) | sK0 = k2_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f146,f56])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v3_funct_2(sK2,X0,sK0) | sK0 = k2_relat_1(sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f145,f53])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 = k2_relat_1(sK2) | ~v3_funct_2(sK2,X0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 0.21/0.52    inference(resolution,[],[f136,f81])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ~v2_funct_2(sK2,sK0) | sK0 = k2_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f126,f56])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.52    inference(resolution,[],[f69,f75])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK2)),
% 0.21/0.52    inference(forward_demodulation,[],[f297,f259])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) | k1_xboole_0 != k1_relat_1(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f266,f260])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    v1_funct_1(k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f53,f259])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) | k1_xboole_0 != k1_relat_1(sK2)),
% 0.21/0.52    inference(backward_demodulation,[],[f192,f259])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~v1_funct_1(k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) | sK2 = k2_funct_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK2)),
% 0.21/0.52    inference(forward_demodulation,[],[f191,f101])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) | sK2 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) != k1_relat_1(sK2)),
% 0.21/0.52    inference(forward_demodulation,[],[f190,f87])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    k6_partfun1(k1_xboole_0) != k5_relat_1(k1_xboole_0,sK2) | sK2 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) != k1_relat_1(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f189,f99])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    k6_partfun1(k1_xboole_0) != k5_relat_1(k1_xboole_0,sK2) | sK2 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) != k1_relat_1(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f185,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    v2_funct_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f88,f87])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f62,f60])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    k6_partfun1(k1_xboole_0) != k5_relat_1(k1_xboole_0,sK2) | sK2 = k2_funct_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) != k1_relat_1(sK2)),
% 0.21/0.52    inference(superposition,[],[f180,f102])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ( ! [X0] : (k6_partfun1(k1_relat_1(X0)) != k5_relat_1(X0,sK2) | k2_funct_1(X0) = sK2 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != k1_relat_1(sK2)) )),
% 0.21/0.52    inference(resolution,[],[f169,f56])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | k6_partfun1(k1_relat_1(X0)) != k5_relat_1(X0,sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != k1_relat_1(sK2)) )),
% 0.21/0.52    inference(resolution,[],[f153,f75])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ( ! [X1] : (~v1_relat_1(sK2) | k2_relat_1(X1) != k1_relat_1(sK2) | ~v2_funct_1(X1) | k2_funct_1(X1) = sK2 | k5_relat_1(X1,sK2) != k6_partfun1(k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(resolution,[],[f92,f53])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | k2_funct_1(X0) = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f70,f60])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 0.21/0.52    inference(backward_demodulation,[],[f271,f338])).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    k1_xboole_0 = sK1),
% 0.21/0.52    inference(resolution,[],[f231,f209])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.52    inference(backward_demodulation,[],[f52,f206])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK1) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f218])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f156,f206])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(superposition,[],[f115,f155])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f216,f259])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f151,f206])).
% 0.21/0.52  % (23589)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.52    inference(superposition,[],[f64,f87])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (23607)------------------------------
% 0.21/0.52  % (23607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23607)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (23607)Memory used [KB]: 6524
% 0.21/0.52  % (23607)Time elapsed: 0.056 s
% 0.21/0.52  % (23607)------------------------------
% 0.21/0.52  % (23607)------------------------------
% 0.21/0.52  % (23579)Success in time 0.164 s
%------------------------------------------------------------------------------
