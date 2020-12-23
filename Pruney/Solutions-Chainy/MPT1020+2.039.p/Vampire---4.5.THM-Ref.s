%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  158 (2608 expanded)
%              Number of leaves         :   18 ( 771 expanded)
%              Depth                    :   30
%              Number of atoms          :  633 (20976 expanded)
%              Number of equality atoms :  163 (1056 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f738,plain,(
    $false ),
    inference(subsumption_resolution,[],[f735,f100])).

fof(f100,plain,(
    v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f73,f91])).

fof(f91,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f86,f58])).

fof(f58,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f60,f59])).

fof(f59,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f735,plain,(
    ~ v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f678,f609])).

fof(f609,plain,(
    v2_funct_2(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f507,f591])).

fof(f591,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f520])).

fof(f520,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f222,f495])).

fof(f495,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f494,f97])).

fof(f97,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f73,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f494,plain,
    ( k1_xboole_0 = sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f490])).

fof(f490,plain,
    ( k1_xboole_0 = sK0
    | sK0 != sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f184,f134])).

fof(f134,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f133,f48])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f133,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f129,f50])).

fof(f50,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f129,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f76,f51])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f184,plain,(
    ! [X0] :
      ( ~ v2_funct_2(sK1,X0)
      | k1_xboole_0 = sK0
      | sK0 != X0
      | ~ v5_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f183,f92])).

fof(f92,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f183,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = sK0
      | ~ v2_funct_2(sK1,X0)
      | ~ v5_relat_1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f181,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f181,plain,
    ( sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f175,f102])).

fof(f102,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f84,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f175,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0
    | sK0 != k2_relat_1(sK1) ),
    inference(superposition,[],[f148,f169])).

fof(f169,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f168,f51])).

fof(f168,plain,
    ( sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f167,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f167,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f166,f48])).

fof(f166,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f165,f49])).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f165,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f164,f51])).

fof(f164,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f163,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f163,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f162,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f162,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f161,f55])).

fof(f161,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f90,f85])).

fof(f85,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f56,f59])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f89,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f77,f59])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f89,plain,(
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
    inference(forward_demodulation,[],[f79,f59])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f40])).

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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f148,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f57,f147])).

fof(f147,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f146,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f145,f49])).

fof(f145,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f141,f50])).

fof(f141,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f70,f51])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f222,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f221,f97])).

fof(f221,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f218,f92])).

fof(f218,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 != sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f116,f134])).

fof(f116,plain,(
    ! [X2,X3] :
      ( ~ v2_funct_2(X2,X3)
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X2)
      | k1_xboole_0 != X3
      | ~ v5_relat_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X2)
      | ~ v2_funct_2(X2,X3)
      | ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f62,f68])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f507,plain,(
    v2_funct_2(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f134,f495])).

fof(f678,plain,(
    ! [X0] :
      ( ~ v2_funct_2(k1_xboole_0,X0)
      | ~ v5_relat_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f677,f662])).

fof(f662,plain,(
    ! [X4] :
      ( ~ v2_funct_2(k1_xboole_0,X4)
      | ~ v5_relat_1(k1_xboole_0,X4)
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f661,f591])).

fof(f661,plain,(
    ! [X4] :
      ( ~ v2_funct_2(k1_xboole_0,X4)
      | k1_xboole_0 = X4
      | ~ v5_relat_1(sK1,X4) ) ),
    inference(forward_demodulation,[],[f535,f591])).

fof(f535,plain,(
    ! [X4] :
      ( k1_xboole_0 = X4
      | ~ v2_funct_2(sK1,X4)
      | ~ v5_relat_1(sK1,X4) ) ),
    inference(backward_demodulation,[],[f264,f495])).

fof(f264,plain,(
    ! [X4] :
      ( ~ v2_funct_2(sK1,X4)
      | sK0 = X4
      | ~ v5_relat_1(sK1,X4) ) ),
    inference(subsumption_resolution,[],[f263,f92])).

fof(f263,plain,(
    ! [X4] :
      ( sK0 = X4
      | ~ v1_relat_1(sK1)
      | ~ v2_funct_2(sK1,X4)
      | ~ v5_relat_1(sK1,X4) ) ),
    inference(subsumption_resolution,[],[f259,f97])).

fof(f259,plain,(
    ! [X4] :
      ( sK0 = X4
      | ~ v5_relat_1(sK1,sK0)
      | ~ v1_relat_1(sK1)
      | ~ v2_funct_2(sK1,X4)
      | ~ v5_relat_1(sK1,X4) ) ),
    inference(resolution,[],[f118,f134])).

fof(f118,plain,(
    ! [X4,X2,X3] :
      ( ~ v2_funct_2(X2,X4)
      | X3 = X4
      | ~ v5_relat_1(X2,X4)
      | ~ v1_relat_1(X2)
      | ~ v2_funct_2(X2,X3)
      | ~ v5_relat_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X4,X2,X3] :
      ( X3 = X4
      | ~ v2_funct_2(X2,X4)
      | ~ v5_relat_1(X2,X4)
      | ~ v1_relat_1(X2)
      | ~ v2_funct_2(X2,X3)
      | ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f68,f68])).

fof(f677,plain,(
    ! [X0] :
      ( ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v2_funct_2(k1_xboole_0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f676,f591])).

fof(f676,plain,(
    ! [X0] :
      ( ~ v2_funct_2(k1_xboole_0,X0)
      | k1_xboole_0 != X0
      | ~ v5_relat_1(sK1,X0) ) ),
    inference(forward_demodulation,[],[f571,f591])).

fof(f571,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ v2_funct_2(sK1,X0)
      | ~ v5_relat_1(sK1,X0) ) ),
    inference(trivial_inequality_removal,[],[f544])).

fof(f544,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 != X0
      | ~ v2_funct_2(sK1,X0)
      | ~ v5_relat_1(sK1,X0) ) ),
    inference(backward_demodulation,[],[f309,f495])).

fof(f309,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 != sK0
      | ~ v2_funct_2(sK1,X0)
      | ~ v5_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f307,f92])).

fof(f307,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 != sK0
      | ~ v2_funct_2(sK1,X0)
      | ~ v5_relat_1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f284,f68])).

fof(f284,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f282,f232])).

fof(f232,plain,
    ( r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f101,f222])).

fof(f101,plain,(
    r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f84,f51])).

fof(f282,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f200,f224])).

fof(f224,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f223,f98])).

fof(f98,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f73,f55])).

fof(f223,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK0
    | ~ v5_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f219,f93])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f71,f55])).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 != sK0
    | ~ v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f116,f136])).

fof(f136,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f135,f52])).

fof(f135,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f130,f54])).

fof(f54,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f130,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f76,f55])).

fof(f200,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f199,f92])).

fof(f199,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f198,f48])).

fof(f198,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f192,f126])).

fof(f126,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f125,f48])).

fof(f125,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f121,f50])).

fof(f121,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f75,f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f192,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f148,f106])).

fof(f106,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_funct_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f105,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f105,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f61,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:49:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (24544)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (24546)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (24550)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24562)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (24553)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (24559)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (24554)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (24558)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (24571)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (24545)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (24558)Refutation not found, incomplete strategy% (24558)------------------------------
% 0.21/0.54  % (24558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24558)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24558)Memory used [KB]: 1791
% 0.21/0.54  % (24558)Time elapsed: 0.118 s
% 0.21/0.54  % (24558)------------------------------
% 0.21/0.54  % (24558)------------------------------
% 0.21/0.54  % (24547)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (24572)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (24557)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (24551)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (24563)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (24554)Refutation not found, incomplete strategy% (24554)------------------------------
% 0.21/0.55  % (24554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24554)Memory used [KB]: 11129
% 0.21/0.55  % (24554)Time elapsed: 0.124 s
% 0.21/0.55  % (24554)------------------------------
% 0.21/0.55  % (24554)------------------------------
% 0.21/0.56  % (24569)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (24552)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (24555)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (24566)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (24561)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (24548)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (24571)Refutation not found, incomplete strategy% (24571)------------------------------
% 0.21/0.57  % (24571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (24571)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24571)Memory used [KB]: 6396
% 0.21/0.57  % (24571)Time elapsed: 0.158 s
% 0.21/0.57  % (24571)------------------------------
% 0.21/0.57  % (24571)------------------------------
% 0.21/0.57  % (24572)Refutation not found, incomplete strategy% (24572)------------------------------
% 0.21/0.57  % (24572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (24572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24572)Memory used [KB]: 11129
% 0.21/0.57  % (24572)Time elapsed: 0.147 s
% 0.21/0.57  % (24572)------------------------------
% 0.21/0.57  % (24572)------------------------------
% 0.21/0.57  % (24568)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  % (24564)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.57  % (24570)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (24553)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f738,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f735,f100])).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    v5_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f73,f91])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.57    inference(superposition,[],[f86,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f60,f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.57  fof(f735,plain,(
% 0.21/0.57    ~v5_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f678,f609])).
% 0.21/0.57  fof(f609,plain,(
% 0.21/0.57    v2_funct_2(k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(backward_demodulation,[],[f507,f591])).
% 0.21/0.57  fof(f591,plain,(
% 0.21/0.57    k1_xboole_0 = sK1),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f520])).
% 0.21/0.57  fof(f520,plain,(
% 0.21/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.21/0.57    inference(backward_demodulation,[],[f222,f495])).
% 0.21/0.57  fof(f495,plain,(
% 0.21/0.57    k1_xboole_0 = sK0),
% 0.21/0.57    inference(subsumption_resolution,[],[f494,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    v5_relat_1(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f73,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f44,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.58    inference(flattening,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.58    inference(negated_conjecture,[],[f16])).
% 0.21/0.58  fof(f16,conjecture,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 0.21/0.58  fof(f494,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | ~v5_relat_1(sK1,sK0)),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f490])).
% 0.21/0.58  fof(f490,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | sK0 != sK0 | ~v5_relat_1(sK1,sK0)),
% 0.21/0.58    inference(resolution,[],[f184,f134])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    v2_funct_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f133,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    v1_funct_1(sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f133,plain,(
% 0.21/0.58    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f129,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 0.21/0.58    inference(resolution,[],[f76,f51])).
% 0.21/0.58  fof(f76,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(flattening,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.58  fof(f184,plain,(
% 0.21/0.58    ( ! [X0] : (~v2_funct_2(sK1,X0) | k1_xboole_0 = sK0 | sK0 != X0 | ~v5_relat_1(sK1,X0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f183,f92])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    v1_relat_1(sK1)),
% 0.21/0.58    inference(resolution,[],[f71,f51])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.58  fof(f183,plain,(
% 0.21/0.58    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = sK0 | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1)) )),
% 0.21/0.58    inference(superposition,[],[f181,f68])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(flattening,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.58  fof(f181,plain,(
% 0.21/0.58    sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.58    inference(subsumption_resolution,[],[f175,f102])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.21/0.58    inference(resolution,[],[f84,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(equality_resolution,[],[f81])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(nnf_transformation,[],[f42])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(flattening,[],[f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.58  fof(f175,plain,(
% 0.21/0.58    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0 | sK0 != k2_relat_1(sK1)),
% 0.21/0.58    inference(superposition,[],[f148,f169])).
% 0.21/0.58  fof(f169,plain,(
% 0.21/0.58    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relat_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f168,f51])).
% 0.21/0.58  fof(f168,plain,(
% 0.21/0.58    sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.58    inference(superposition,[],[f167,f72])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.58  fof(f167,plain,(
% 0.21/0.58    sK0 != k2_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f166,f48])).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f165,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f164,f51])).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f163,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    v1_funct_1(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f163,plain,(
% 0.21/0.58    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f162,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f162,plain,(
% 0.21/0.58    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f161,f55])).
% 0.21/0.58  fof(f161,plain,(
% 0.21/0.58    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.58  fof(f159,plain,(
% 0.21/0.58    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(resolution,[],[f90,f85])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 0.21/0.58    inference(forward_demodulation,[],[f56,f59])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f89,f88])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f77,f59])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.58    inference(flattening,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f79,f59])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.58    inference(flattening,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.58  fof(f148,plain,(
% 0.21/0.58    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 0.21/0.58    inference(backward_demodulation,[],[f57,f147])).
% 0.21/0.58  fof(f147,plain,(
% 0.21/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f146,f48])).
% 0.21/0.58  fof(f146,plain,(
% 0.21/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f145,f49])).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f141,f50])).
% 0.21/0.58  fof(f141,plain,(
% 0.21/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.58    inference(resolution,[],[f70,f51])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.58    inference(flattening,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f222,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.21/0.58    inference(subsumption_resolution,[],[f221,f97])).
% 0.21/0.58  fof(f221,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | k1_xboole_0 != sK0 | ~v5_relat_1(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f218,f92])).
% 0.21/0.58  fof(f218,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | k1_xboole_0 != sK0 | ~v5_relat_1(sK1,sK0)),
% 0.21/0.58    inference(resolution,[],[f116,f134])).
% 0.21/0.58  fof(f116,plain,(
% 0.21/0.58    ( ! [X2,X3] : (~v2_funct_2(X2,X3) | k1_xboole_0 = X2 | ~v1_relat_1(X2) | k1_xboole_0 != X3 | ~v5_relat_1(X2,X3)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f114])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    ( ! [X2,X3] : (k1_xboole_0 != X3 | k1_xboole_0 = X2 | ~v1_relat_1(X2) | ~v2_funct_2(X2,X3) | ~v5_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 0.21/0.58    inference(superposition,[],[f62,f68])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.58  fof(f507,plain,(
% 0.21/0.58    v2_funct_2(sK1,k1_xboole_0)),
% 0.21/0.58    inference(backward_demodulation,[],[f134,f495])).
% 0.21/0.58  fof(f678,plain,(
% 0.21/0.58    ( ! [X0] : (~v2_funct_2(k1_xboole_0,X0) | ~v5_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f677,f662])).
% 0.21/0.58  fof(f662,plain,(
% 0.21/0.58    ( ! [X4] : (~v2_funct_2(k1_xboole_0,X4) | ~v5_relat_1(k1_xboole_0,X4) | k1_xboole_0 = X4) )),
% 0.21/0.58    inference(forward_demodulation,[],[f661,f591])).
% 0.21/0.58  fof(f661,plain,(
% 0.21/0.58    ( ! [X4] : (~v2_funct_2(k1_xboole_0,X4) | k1_xboole_0 = X4 | ~v5_relat_1(sK1,X4)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f535,f591])).
% 0.21/0.58  fof(f535,plain,(
% 0.21/0.58    ( ! [X4] : (k1_xboole_0 = X4 | ~v2_funct_2(sK1,X4) | ~v5_relat_1(sK1,X4)) )),
% 0.21/0.58    inference(backward_demodulation,[],[f264,f495])).
% 0.21/0.58  fof(f264,plain,(
% 0.21/0.58    ( ! [X4] : (~v2_funct_2(sK1,X4) | sK0 = X4 | ~v5_relat_1(sK1,X4)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f263,f92])).
% 0.21/0.58  fof(f263,plain,(
% 0.21/0.58    ( ! [X4] : (sK0 = X4 | ~v1_relat_1(sK1) | ~v2_funct_2(sK1,X4) | ~v5_relat_1(sK1,X4)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f259,f97])).
% 0.21/0.58  fof(f259,plain,(
% 0.21/0.58    ( ! [X4] : (sK0 = X4 | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~v2_funct_2(sK1,X4) | ~v5_relat_1(sK1,X4)) )),
% 0.21/0.58    inference(resolution,[],[f118,f134])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    ( ! [X4,X2,X3] : (~v2_funct_2(X2,X4) | X3 = X4 | ~v5_relat_1(X2,X4) | ~v1_relat_1(X2) | ~v2_funct_2(X2,X3) | ~v5_relat_1(X2,X3)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    ( ! [X4,X2,X3] : (X3 = X4 | ~v2_funct_2(X2,X4) | ~v5_relat_1(X2,X4) | ~v1_relat_1(X2) | ~v2_funct_2(X2,X3) | ~v5_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 0.21/0.58    inference(superposition,[],[f68,f68])).
% 0.21/0.58  fof(f677,plain,(
% 0.21/0.58    ( ! [X0] : (~v5_relat_1(k1_xboole_0,X0) | ~v2_funct_2(k1_xboole_0,X0) | k1_xboole_0 != X0) )),
% 0.21/0.58    inference(forward_demodulation,[],[f676,f591])).
% 0.21/0.58  fof(f676,plain,(
% 0.21/0.58    ( ! [X0] : (~v2_funct_2(k1_xboole_0,X0) | k1_xboole_0 != X0 | ~v5_relat_1(sK1,X0)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f571,f591])).
% 0.21/0.58  fof(f571,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != X0 | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0)) )),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f544])).
% 0.21/0.58  fof(f544,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != X0 | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0)) )),
% 0.21/0.58    inference(backward_demodulation,[],[f309,f495])).
% 0.21/0.58  fof(f309,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 != sK0 | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f307,f92])).
% 0.21/0.58  fof(f307,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 != sK0 | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1)) )),
% 0.21/0.58    inference(superposition,[],[f284,f68])).
% 0.21/0.58  fof(f284,plain,(
% 0.21/0.58    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 != sK0),
% 0.21/0.58    inference(subsumption_resolution,[],[f282,f232])).
% 0.21/0.58  fof(f232,plain,(
% 0.21/0.58    r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0),
% 0.21/0.58    inference(superposition,[],[f101,f222])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    r2_relset_1(sK0,sK0,sK1,sK1)),
% 0.21/0.58    inference(resolution,[],[f84,f51])).
% 0.21/0.58  fof(f282,plain,(
% 0.21/0.58    ~r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 != sK0),
% 0.21/0.58    inference(superposition,[],[f200,f224])).
% 0.21/0.58  fof(f224,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | k1_xboole_0 != sK0),
% 0.21/0.58    inference(subsumption_resolution,[],[f223,f98])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    v5_relat_1(sK2,sK0)),
% 0.21/0.58    inference(resolution,[],[f73,f55])).
% 0.21/0.58  fof(f223,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | k1_xboole_0 != sK0 | ~v5_relat_1(sK2,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f219,f93])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    v1_relat_1(sK2)),
% 0.21/0.58    inference(resolution,[],[f71,f55])).
% 0.21/0.58  fof(f219,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | k1_xboole_0 != sK0 | ~v5_relat_1(sK2,sK0)),
% 0.21/0.58    inference(resolution,[],[f116,f136])).
% 0.21/0.58  fof(f136,plain,(
% 0.21/0.58    v2_funct_2(sK2,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f135,f52])).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f130,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f130,plain,(
% 0.21/0.58    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 0.21/0.58    inference(resolution,[],[f76,f55])).
% 0.21/0.58  fof(f200,plain,(
% 0.21/0.58    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f199,f92])).
% 0.21/0.58  fof(f199,plain,(
% 0.21/0.58    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f198,f48])).
% 0.21/0.58  fof(f198,plain,(
% 0.21/0.58    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f192,f126])).
% 0.21/0.58  fof(f126,plain,(
% 0.21/0.58    v2_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f125,f48])).
% 0.21/0.58  fof(f125,plain,(
% 0.21/0.58    ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f121,f50])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.21/0.58    inference(resolution,[],[f75,f51])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 0.21/0.58  fof(f192,plain,(
% 0.21/0.58    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.58    inference(superposition,[],[f148,f106])).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k2_funct_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f105,f63])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(superposition,[],[f61,f66])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (24553)------------------------------
% 0.21/0.58  % (24553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (24553)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (24553)Memory used [KB]: 1918
% 0.21/0.58  % (24553)Time elapsed: 0.155 s
% 0.21/0.58  % (24553)------------------------------
% 0.21/0.58  % (24553)------------------------------
% 0.21/0.58  % (24543)Success in time 0.212 s
%------------------------------------------------------------------------------
