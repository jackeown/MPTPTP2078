%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  185 (9333 expanded)
%              Number of leaves         :   19 (2830 expanded)
%              Depth                    :   31
%              Number of atoms          :  678 (76996 expanded)
%              Number of equality atoms :  193 (3031 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f521,plain,(
    $false ),
    inference(subsumption_resolution,[],[f518,f375])).

fof(f375,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f308,f356])).

fof(f356,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f353])).

fof(f353,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f296,f299])).

fof(f299,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f298,f121])).

fof(f121,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f94,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f50,f49])).

fof(f49,plain,
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

fof(f50,plain,
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f298,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f150,f269])).

fof(f269,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f268,f230])).

fof(f230,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f95,f227])).

fof(f227,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f224,f55])).

fof(f55,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f224,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f163,f58])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f163,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK0,sK0,X5,sK2) = k5_relat_1(X5,sK2)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f160,f59])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f160,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK0,sK0,X5,sK2) = k5_relat_1(X5,sK2)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f89,f62])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f95,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f63,f66])).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f63,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f268,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(forward_demodulation,[],[f267,f227])).

fof(f267,plain,
    ( k1_xboole_0 = sK0
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f266,f55])).

fof(f266,plain,
    ( k1_xboole_0 = sK0
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f265,f58])).

fof(f265,plain,
    ( k1_xboole_0 = sK0
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f263,f195])).

fof(f195,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f123,f193])).

fof(f193,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f192,f101])).

fof(f101,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f78,f58])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f192,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f191,f106])).

fof(f106,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f80,f58])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f191,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f136,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f136,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f135,f58])).

fof(f135,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f133,f55])).

fof(f133,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f123,plain,(
    k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f263,plain,
    ( k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f187,f56])).

fof(f56,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f187,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,sK0,sK0)
      | k1_xboole_0 = sK0
      | sK0 != k2_relset_1(sK0,sK0,X1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k2_funct_1(X1) = sK2
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f186,f59])).

fof(f186,plain,(
    ! [X1] :
      ( k2_funct_1(X1) = sK2
      | k1_xboole_0 = sK0
      | sK0 != k2_relset_1(sK0,sK0,X1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f182,f62])).

fof(f182,plain,(
    ! [X1] :
      ( k2_funct_1(X1) = sK2
      | k1_xboole_0 = sK0
      | sK0 != k2_relset_1(sK0,sK0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X1] :
      ( k2_funct_1(X1) = sK2
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | sK0 != k2_relset_1(sK0,sK0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f100,f60])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f99,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f84,f66])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f86,f66])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f150,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f64,f149])).

fof(f149,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f148,f55])).

fof(f148,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f147,f57])).

fof(f147,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f145,f58])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f77,f56])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f64,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f296,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f109,f193])).

fof(f109,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f101,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f308,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK1) ),
    inference(backward_demodulation,[],[f120,f299])).

fof(f120,plain,(
    r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f94,f58])).

fof(f518,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f441,f517])).

fof(f517,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f516,f363])).

fof(f363,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f101,f356])).

fof(f516,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f515,f382])).

fof(f382,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f325,f356])).

fof(f325,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(backward_demodulation,[],[f193,f299])).

fof(f515,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f513,f444])).

fof(f444,plain,(
    k6_relat_1(k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f405,f355])).

fof(f355,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f354])).

fof(f354,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f297,f299])).

fof(f297,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f141,f198])).

fof(f198,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f197,f102])).

fof(f102,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f62])).

fof(f197,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f196,f107])).

fof(f107,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f80,f62])).

fof(f196,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f138,f75])).

fof(f138,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f137,f62])).

fof(f137,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f134,f59])).

fof(f134,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f83,f61])).

fof(f61,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f141,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f102,f71])).

fof(f405,plain,(
    k6_relat_1(k1_xboole_0) = k5_relat_1(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f404,f356])).

fof(f404,plain,(
    k6_relat_1(k1_xboole_0) = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f399,f394])).

fof(f394,plain,(
    m1_subset_1(k5_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f345,f356])).

fof(f345,plain,(
    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f246,f299])).

fof(f246,plain,(
    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f245,f227])).

fof(f245,plain,(
    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f242,f55])).

fof(f242,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f168,f58])).

fof(f168,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f165,f59])).

fof(f165,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f91,f62])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f399,plain,
    ( ~ m1_subset_1(k5_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k6_relat_1(k1_xboole_0) = k5_relat_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f361,f356])).

fof(f361,plain,
    ( k6_relat_1(k1_xboole_0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f339,f299])).

fof(f339,plain,
    ( ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k6_relat_1(sK0) = k5_relat_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f231,f299])).

fof(f231,plain,
    ( ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK1,sK2) ),
    inference(forward_demodulation,[],[f229,f227])).

fof(f229,plain,
    ( ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f144,f227])).

fof(f144,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f143,f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f67,f66])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f143,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f87,f95])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f513,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k6_relat_1(k1_xboole_0) != k5_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f448,f362])).

fof(f362,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f55,f356])).

fof(f448,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_funct_1(k1_xboole_0) = X0
      | k6_relat_1(k1_xboole_0) != k5_relat_1(X0,k1_xboole_0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f403,f447])).

fof(f447,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f446,f355])).

fof(f446,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f413,f382])).

fof(f413,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f139,f355])).

fof(f139,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f102,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_relat_1(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f403,plain,(
    ! [X0] :
      ( k2_funct_1(k1_xboole_0) = X0
      | k6_relat_1(k1_xboole_0) != k5_relat_1(X0,k1_xboole_0)
      | k2_relat_1(X0) != k1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f402,f356])).

fof(f402,plain,(
    ! [X0] :
      ( k6_relat_1(k1_xboole_0) != k5_relat_1(X0,k1_xboole_0)
      | k2_relat_1(X0) != k1_relat_1(k1_xboole_0)
      | k2_funct_1(sK1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f383,f356])).

fof(f383,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != k1_relat_1(k1_xboole_0)
      | k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK1)
      | k2_funct_1(sK1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f326,f356])).

fof(f326,plain,(
    ! [X0] :
      ( k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK1)
      | k2_relat_1(X0) != k1_relat_1(sK1)
      | k2_funct_1(sK1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f194,f299])).

fof(f194,plain,(
    ! [X0] :
      ( k6_relat_1(sK0) != k5_relat_1(X0,sK1)
      | k2_relat_1(X0) != k1_relat_1(sK1)
      | k2_funct_1(sK1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f177,f193])).

fof(f177,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK1) != k6_relat_1(k2_relat_1(sK1))
      | k2_relat_1(X0) != k1_relat_1(sK1)
      | k2_funct_1(sK1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f176,f101])).

fof(f176,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK1) != k6_relat_1(k2_relat_1(sK1))
      | k2_relat_1(X0) != k1_relat_1(sK1)
      | k2_funct_1(sK1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f175,f55])).

fof(f175,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK1) != k6_relat_1(k2_relat_1(sK1))
      | k2_relat_1(X0) != k1_relat_1(sK1)
      | k2_funct_1(sK1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f130,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f130,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f129,f58])).

fof(f129,plain,
    ( v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f127,f55])).

fof(f127,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f82,f57])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f441,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f378,f355])).

fof(f378,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f313,f356])).

fof(f313,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f150,f299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (31950)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.48  % (31959)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.49  % (31959)Refutation not found, incomplete strategy% (31959)------------------------------
% 0.21/0.49  % (31959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31959)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31959)Memory used [KB]: 10746
% 0.21/0.49  % (31959)Time elapsed: 0.079 s
% 0.21/0.49  % (31959)------------------------------
% 0.21/0.49  % (31959)------------------------------
% 0.21/0.49  % (31950)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f521,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f518,f375])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f308,f356])).
% 0.21/0.49  fof(f356,plain,(
% 0.21/0.49    k1_xboole_0 = sK1),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f353])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.21/0.49    inference(backward_demodulation,[],[f296,f299])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f298,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f94,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f50,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f19])).
% 0.21/0.49  fof(f19,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(superposition,[],[f150,f269])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f268,f230])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f95,f227])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f163,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK0,sK0,X5,sK2) = k5_relat_1(X5,sK2) | ~v1_funct_1(X5)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f160,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK0,sK0,X5,sK2) = k5_relat_1(X5,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 0.21/0.49    inference(resolution,[],[f89,f62])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.49    inference(flattening,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f63,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f267,f227])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | sK2 = k2_funct_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f266,f55])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f265,f58])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f263,f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.49    inference(backward_demodulation,[],[f123,f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    sK0 = k2_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f192,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f78,f58])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f191,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    v5_relat_1(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f80,f58])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f136,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    v2_funct_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f135,f58])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    v2_funct_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f133,f55])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    v2_funct_2(sK1,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(resolution,[],[f83,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f79,f58])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.50    inference(resolution,[],[f187,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_funct_2(X1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,X1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_1(X1) = sK2 | ~v1_funct_1(X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f59])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X1] : (k2_funct_1(X1) = sK2 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,X1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X1,sK0,sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f182,f62])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ( ! [X1] : (k2_funct_1(X1) = sK2 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X1,sK0,sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f181])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X1] : (k2_funct_1(X1) = sK2 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X1,sK2),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X1,sK0,sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.50    inference(resolution,[],[f100,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f99,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f84,f66])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f86,f66])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 0.21/0.50    inference(backward_demodulation,[],[f64,f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f55])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f147,f57])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f145,f58])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.50    inference(resolution,[],[f77,f56])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f109,f193])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(resolution,[],[f101,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f120,f299])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    r2_relset_1(sK0,sK0,sK1,sK1)),
% 0.21/0.50    inference(resolution,[],[f94,f58])).
% 0.21/0.50  fof(f518,plain,(
% 0.21/0.50    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f441,f517])).
% 0.21/0.50  fof(f517,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f516,f363])).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    v1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f101,f356])).
% 0.21/0.50  fof(f516,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f515,f382])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f325,f356])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f193,f299])).
% 0.21/0.50  fof(f515,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f513,f444])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    k6_relat_1(k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f405,f355])).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    k1_xboole_0 = sK2),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f354])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 0.21/0.50    inference(backward_demodulation,[],[f297,f299])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    k1_xboole_0 != sK0 | k1_xboole_0 = sK2),
% 0.21/0.50    inference(superposition,[],[f141,f198])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    sK0 = k2_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f197,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f78,f62])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f196,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    v5_relat_1(sK2,sK0)),
% 0.21/0.50    inference(resolution,[],[f80,f62])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f138,f75])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    v2_funct_2(sK2,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f137,f62])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    v2_funct_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f134,f59])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    v2_funct_2(sK2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(resolution,[],[f83,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.21/0.50    inference(resolution,[],[f102,f71])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    k6_relat_1(k1_xboole_0) = k5_relat_1(k1_xboole_0,sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f404,f356])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    k6_relat_1(k1_xboole_0) = k5_relat_1(sK1,sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f399,f394])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    m1_subset_1(k5_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f345,f356])).
% 0.21/0.50  fof(f345,plain,(
% 0.21/0.50    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f246,f299])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f245,f227])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f242,f55])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.21/0.50    inference(resolution,[],[f168,f58])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(X5)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f165,f59])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 0.21/0.50    inference(resolution,[],[f91,f62])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.50    inference(flattening,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    ~m1_subset_1(k5_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_relat_1(k1_xboole_0) = k5_relat_1(sK1,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f361,f356])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    k6_relat_1(k1_xboole_0) = k5_relat_1(sK1,sK2) | ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f339,f299])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_relat_1(sK0) = k5_relat_1(sK1,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f231,f299])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK1,sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f229,f227])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f144,f227])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f143,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f67,f66])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(resolution,[],[f87,f95])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f54])).
% 0.21/0.50  fof(f513,plain,(
% 0.21/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k6_relat_1(k1_xboole_0) != k5_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f448,f362])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    v1_funct_1(k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f55,f356])).
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | k2_funct_1(k1_xboole_0) = X0 | k6_relat_1(k1_xboole_0) != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f403,f447])).
% 0.21/0.50  fof(f447,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(forward_demodulation,[],[f446,f355])).
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f413,f382])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f139,f355])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f102,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    ( ! [X0] : (k2_funct_1(k1_xboole_0) = X0 | k6_relat_1(k1_xboole_0) != k5_relat_1(X0,k1_xboole_0) | k2_relat_1(X0) != k1_relat_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f402,f356])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    ( ! [X0] : (k6_relat_1(k1_xboole_0) != k5_relat_1(X0,k1_xboole_0) | k2_relat_1(X0) != k1_relat_1(k1_xboole_0) | k2_funct_1(sK1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f383,f356])).
% 0.21/0.50  fof(f383,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(X0) != k1_relat_1(k1_xboole_0) | k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK1) | k2_funct_1(sK1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f326,f356])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    ( ! [X0] : (k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK1) | k2_relat_1(X0) != k1_relat_1(sK1) | k2_funct_1(sK1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f194,f299])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X0] : (k6_relat_1(sK0) != k5_relat_1(X0,sK1) | k2_relat_1(X0) != k1_relat_1(sK1) | k2_funct_1(sK1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f177,f193])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relat_1(X0,sK1) != k6_relat_1(k2_relat_1(sK1)) | k2_relat_1(X0) != k1_relat_1(sK1) | k2_funct_1(sK1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f176,f101])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relat_1(X0,sK1) != k6_relat_1(k2_relat_1(sK1)) | k2_relat_1(X0) != k1_relat_1(sK1) | k2_funct_1(sK1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f175,f55])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relat_1(X0,sK1) != k6_relat_1(k2_relat_1(sK1)) | k2_relat_1(X0) != k1_relat_1(sK1) | k2_funct_1(sK1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.50    inference(resolution,[],[f130,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_funct_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    v2_funct_1(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f129,f58])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f127,f55])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(resolution,[],[f82,f57])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f441,plain,(
% 0.21/0.50    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 0.21/0.50    inference(backward_demodulation,[],[f378,f355])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))),
% 0.21/0.50    inference(backward_demodulation,[],[f313,f356])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 0.21/0.50    inference(backward_demodulation,[],[f150,f299])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (31950)------------------------------
% 0.21/0.50  % (31950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31950)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (31950)Memory used [KB]: 2046
% 0.21/0.50  % (31950)Time elapsed: 0.081 s
% 0.21/0.50  % (31950)------------------------------
% 0.21/0.50  % (31950)------------------------------
% 0.21/0.50  % (31965)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (31942)Success in time 0.141 s
%------------------------------------------------------------------------------
