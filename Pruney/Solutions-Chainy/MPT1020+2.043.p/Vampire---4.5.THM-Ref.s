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
% DateTime   : Thu Dec  3 13:05:46 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 586 expanded)
%              Number of leaves         :   16 ( 171 expanded)
%              Depth                    :   24
%              Number of atoms          :  516 (4564 expanded)
%              Number of equality atoms :  134 ( 218 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(subsumption_resolution,[],[f226,f81])).

fof(f81,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f61,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f38])).

% (9899)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
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
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f226,plain,(
    ~ v5_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f222,f203])).

fof(f203,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f202,f148])).

fof(f148,plain,
    ( r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f83,f138])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f137,f81])).

fof(f137,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f134,f79])).

fof(f79,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f59,f44])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f134,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 != sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f88,f100])).

fof(f100,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f97,f43])).

fof(f43,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f88,plain,(
    ! [X2,X3] :
      ( ~ v2_funct_2(X2,X3)
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X2)
      | k1_xboole_0 != X3
      | ~ v5_relat_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X2)
      | ~ v2_funct_2(X2,X3)
      | ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (9911)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f83,plain,(
    r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f72,f44])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f202,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f157,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f139,f82])).

fof(f82,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f61,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f139,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK0
    | ~ v5_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f135,f80])).

fof(f80,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f48])).

fof(f135,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 != sK0
    | ~ v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f88,f102])).

fof(f102,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f101,f45])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f98,f47])).

fof(f47,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f64,f48])).

fof(f157,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f152,f78])).

fof(f78,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f53,f51])).

fof(f51,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f152,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0))
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f110,f138])).

fof(f110,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f50,f109])).

fof(f109,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f108,f41])).

fof(f108,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f107,f42])).

fof(f42,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f105,f43])).

fof(f105,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f50,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f222,plain,
    ( k1_xboole_0 = sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f200,f100])).

fof(f200,plain,(
    ! [X0] :
      ( ~ v2_funct_2(sK1,X0)
      | k1_xboole_0 = sK0
      | ~ v5_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f199,f163])).

fof(f163,plain,(
    ! [X2] :
      ( ~ v2_funct_2(sK1,X2)
      | sK0 = X2
      | ~ v5_relat_1(sK1,X2) ) ),
    inference(subsumption_resolution,[],[f162,f79])).

fof(f162,plain,(
    ! [X2] :
      ( sK0 = X2
      | ~ v1_relat_1(sK1)
      | ~ v2_funct_2(sK1,X2)
      | ~ v5_relat_1(sK1,X2) ) ),
    inference(subsumption_resolution,[],[f159,f81])).

fof(f159,plain,(
    ! [X2] :
      ( sK0 = X2
      | ~ v5_relat_1(sK1,sK0)
      | ~ v1_relat_1(sK1)
      | ~ v2_funct_2(sK1,X2)
      | ~ v5_relat_1(sK1,X2) ) ),
    inference(resolution,[],[f90,f100])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_2(X0,X2)
      | X1 = X2
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_2(X0,X1)
      | ~ v5_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v2_funct_2(X0,X2)
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_2(X0,X1)
      | ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f56,f56])).

fof(f199,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = sK0
      | ~ v2_funct_2(sK1,X0)
      | ~ v5_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f198,f79])).

fof(f198,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = sK0
      | ~ v2_funct_2(sK1,X0)
      | ~ v5_relat_1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f196,f56])).

fof(f196,plain,
    ( sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f195,f84])).

fof(f84,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f72,f48])).

fof(f195,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0
    | sK0 != k2_relat_1(sK1) ),
    inference(superposition,[],[f110,f128])).

fof(f128,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f127,f44])).

fof(f127,plain,
    ( sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f126,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f126,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f124,f42])).

fof(f124,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f123,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f122,f45])).

fof(f122,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f121,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
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
    inference(resolution,[],[f77,f73])).

fof(f73,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f49,f52])).

fof(f52,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f49,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
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
    inference(subsumption_resolution,[],[f76,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f65,f52])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f76,plain,(
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
    inference(forward_demodulation,[],[f67,f52])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:57:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.21/0.52  % (9901)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.21/0.52  % (9884)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.21/0.52  % (9897)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.21/0.52  % (9885)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.21/0.52  % (9898)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.21/0.52  % (9893)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.21/0.52  % (9900)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.21/0.52  % (9898)Refutation not found, incomplete strategy% (9898)------------------------------
% 1.21/0.52  % (9898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (9898)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (9898)Memory used [KB]: 1791
% 1.21/0.52  % (9898)Time elapsed: 0.117 s
% 1.21/0.52  % (9898)------------------------------
% 1.21/0.52  % (9898)------------------------------
% 1.21/0.53  % (9893)Refutation found. Thanks to Tanya!
% 1.21/0.53  % SZS status Theorem for theBenchmark
% 1.21/0.53  % (9901)Refutation not found, incomplete strategy% (9901)------------------------------
% 1.21/0.53  % (9901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (9891)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.21/0.53  % (9892)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.21/0.53  % (9887)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.21/0.53  % (9885)Refutation not found, incomplete strategy% (9885)------------------------------
% 1.21/0.53  % (9885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (9886)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.21/0.53  % (9909)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.21/0.53  % (9890)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.53  % SZS output start Proof for theBenchmark
% 1.36/0.53  fof(f227,plain,(
% 1.36/0.53    $false),
% 1.36/0.53    inference(subsumption_resolution,[],[f226,f81])).
% 1.36/0.53  fof(f81,plain,(
% 1.36/0.53    v5_relat_1(sK1,sK0)),
% 1.36/0.53    inference(resolution,[],[f61,f44])).
% 1.36/0.53  fof(f44,plain,(
% 1.36/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  % (9899)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.36/0.53  fof(f38,plain,(
% 1.36/0.53    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f37,f36])).
% 1.36/0.53  fof(f36,plain,(
% 1.36/0.53    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f37,plain,(
% 1.36/0.53    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f18,plain,(
% 1.36/0.53    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.36/0.53    inference(flattening,[],[f17])).
% 1.36/0.53  fof(f17,plain,(
% 1.36/0.53    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.36/0.53    inference(ennf_transformation,[],[f15])).
% 1.36/0.53  fof(f15,negated_conjecture,(
% 1.36/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.36/0.53    inference(negated_conjecture,[],[f14])).
% 1.36/0.53  fof(f14,conjecture,(
% 1.36/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 1.36/0.53  fof(f61,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f27])).
% 1.36/0.53  fof(f27,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(ennf_transformation,[],[f16])).
% 1.36/0.53  fof(f16,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.36/0.53    inference(pure_predicate_removal,[],[f5])).
% 1.36/0.53  fof(f5,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.53  fof(f226,plain,(
% 1.36/0.53    ~v5_relat_1(sK1,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f222,f203])).
% 1.36/0.53  fof(f203,plain,(
% 1.36/0.53    k1_xboole_0 != sK0),
% 1.36/0.53    inference(subsumption_resolution,[],[f202,f148])).
% 1.36/0.53  fof(f148,plain,(
% 1.36/0.53    r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0),
% 1.36/0.53    inference(superposition,[],[f83,f138])).
% 1.36/0.53  fof(f138,plain,(
% 1.36/0.53    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 1.36/0.53    inference(subsumption_resolution,[],[f137,f81])).
% 1.36/0.53  fof(f137,plain,(
% 1.36/0.53    k1_xboole_0 = sK1 | k1_xboole_0 != sK0 | ~v5_relat_1(sK1,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f134,f79])).
% 1.36/0.53  fof(f79,plain,(
% 1.36/0.53    v1_relat_1(sK1)),
% 1.36/0.53    inference(resolution,[],[f59,f44])).
% 1.36/0.53  fof(f59,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f25])).
% 1.36/0.53  fof(f25,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(ennf_transformation,[],[f4])).
% 1.36/0.53  fof(f4,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.53  fof(f134,plain,(
% 1.36/0.53    k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | k1_xboole_0 != sK0 | ~v5_relat_1(sK1,sK0)),
% 1.36/0.53    inference(resolution,[],[f88,f100])).
% 1.36/0.53  fof(f100,plain,(
% 1.36/0.53    v2_funct_2(sK1,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f99,f41])).
% 1.36/0.53  fof(f41,plain,(
% 1.36/0.53    v1_funct_1(sK1)),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f99,plain,(
% 1.36/0.53    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f97,f43])).
% 1.36/0.53  fof(f43,plain,(
% 1.36/0.53    v3_funct_2(sK1,sK0,sK0)),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f97,plain,(
% 1.36/0.53    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.36/0.53    inference(resolution,[],[f64,f44])).
% 1.36/0.53  fof(f64,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f29])).
% 1.36/0.53  fof(f29,plain,(
% 1.36/0.53    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(flattening,[],[f28])).
% 1.36/0.53  fof(f28,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(ennf_transformation,[],[f8])).
% 1.36/0.53  fof(f8,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.36/0.53  fof(f88,plain,(
% 1.36/0.53    ( ! [X2,X3] : (~v2_funct_2(X2,X3) | k1_xboole_0 = X2 | ~v1_relat_1(X2) | k1_xboole_0 != X3 | ~v5_relat_1(X2,X3)) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f87])).
% 1.36/0.53  fof(f87,plain,(
% 1.36/0.53    ( ! [X2,X3] : (k1_xboole_0 != X3 | k1_xboole_0 = X2 | ~v1_relat_1(X2) | ~v2_funct_2(X2,X3) | ~v5_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 1.36/0.53    inference(superposition,[],[f55,f56])).
% 1.36/0.53  fof(f56,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f39])).
% 1.36/0.53  fof(f39,plain,(
% 1.36/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(nnf_transformation,[],[f22])).
% 1.36/0.53  fof(f22,plain,(
% 1.36/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(flattening,[],[f21])).
% 1.36/0.53  fof(f21,plain,(
% 1.36/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.36/0.53    inference(ennf_transformation,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.36/0.53  fof(f55,plain,(
% 1.36/0.53    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f20])).
% 1.36/0.53  fof(f20,plain,(
% 1.36/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(flattening,[],[f19])).
% 1.36/0.53  fof(f19,plain,(
% 1.36/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f1])).
% 1.36/0.53  % (9911)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.53  fof(f1,axiom,(
% 1.36/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.36/0.53  fof(f83,plain,(
% 1.36/0.53    r2_relset_1(sK0,sK0,sK1,sK1)),
% 1.36/0.53    inference(resolution,[],[f72,f44])).
% 1.36/0.53  fof(f72,plain,(
% 1.36/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f71])).
% 1.36/0.53  fof(f71,plain,(
% 1.36/0.53    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.53    inference(equality_resolution,[],[f69])).
% 1.36/0.53  fof(f69,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f40])).
% 1.36/0.53  fof(f40,plain,(
% 1.36/0.53    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(nnf_transformation,[],[f35])).
% 1.36/0.53  fof(f35,plain,(
% 1.36/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(flattening,[],[f34])).
% 1.36/0.53  fof(f34,plain,(
% 1.36/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.36/0.53    inference(ennf_transformation,[],[f7])).
% 1.36/0.53  fof(f7,axiom,(
% 1.36/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.36/0.53  fof(f202,plain,(
% 1.36/0.53    ~r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f201])).
% 1.36/0.53  fof(f201,plain,(
% 1.36/0.53    ~r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0 | k1_xboole_0 != sK0),
% 1.36/0.53    inference(superposition,[],[f157,f140])).
% 1.36/0.53  fof(f140,plain,(
% 1.36/0.53    k1_xboole_0 = sK2 | k1_xboole_0 != sK0),
% 1.36/0.53    inference(subsumption_resolution,[],[f139,f82])).
% 1.36/0.53  fof(f82,plain,(
% 1.36/0.53    v5_relat_1(sK2,sK0)),
% 1.36/0.53    inference(resolution,[],[f61,f48])).
% 1.36/0.53  fof(f48,plain,(
% 1.36/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f139,plain,(
% 1.36/0.53    k1_xboole_0 = sK2 | k1_xboole_0 != sK0 | ~v5_relat_1(sK2,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f135,f80])).
% 1.36/0.53  fof(f80,plain,(
% 1.36/0.53    v1_relat_1(sK2)),
% 1.36/0.53    inference(resolution,[],[f59,f48])).
% 1.36/0.53  fof(f135,plain,(
% 1.36/0.53    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | k1_xboole_0 != sK0 | ~v5_relat_1(sK2,sK0)),
% 1.36/0.53    inference(resolution,[],[f88,f102])).
% 1.36/0.53  fof(f102,plain,(
% 1.36/0.53    v2_funct_2(sK2,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f101,f45])).
% 1.36/0.53  fof(f45,plain,(
% 1.36/0.53    v1_funct_1(sK2)),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f101,plain,(
% 1.36/0.53    ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f98,f47])).
% 1.36/0.53  fof(f47,plain,(
% 1.36/0.53    v3_funct_2(sK2,sK0,sK0)),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f98,plain,(
% 1.36/0.53    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 1.36/0.53    inference(resolution,[],[f64,f48])).
% 1.36/0.53  fof(f157,plain,(
% 1.36/0.53    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | k1_xboole_0 != sK0),
% 1.36/0.53    inference(forward_demodulation,[],[f152,f78])).
% 1.36/0.53  fof(f78,plain,(
% 1.36/0.53    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.36/0.53    inference(superposition,[],[f53,f51])).
% 1.36/0.53  fof(f51,plain,(
% 1.36/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.36/0.53    inference(cnf_transformation,[],[f2])).
% 1.36/0.53  fof(f2,axiom,(
% 1.36/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.36/0.53  fof(f53,plain,(
% 1.36/0.53    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f3])).
% 1.36/0.53  fof(f3,axiom,(
% 1.36/0.53    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 1.36/0.53  fof(f152,plain,(
% 1.36/0.53    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(k1_xboole_0)) | k1_xboole_0 != sK0),
% 1.36/0.53    inference(superposition,[],[f110,f138])).
% 1.36/0.53  fof(f110,plain,(
% 1.36/0.53    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 1.36/0.53    inference(backward_demodulation,[],[f50,f109])).
% 1.36/0.53  fof(f109,plain,(
% 1.36/0.53    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f108,f41])).
% 1.36/0.53  fof(f108,plain,(
% 1.36/0.53    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f107,f42])).
% 1.36/0.53  fof(f42,plain,(
% 1.36/0.53    v1_funct_2(sK1,sK0,sK0)),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f107,plain,(
% 1.36/0.53    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f105,f43])).
% 1.36/0.53  fof(f105,plain,(
% 1.36/0.53    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(resolution,[],[f58,f44])).
% 1.36/0.53  fof(f58,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f24])).
% 1.36/0.53  fof(f24,plain,(
% 1.36/0.53    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.36/0.53    inference(flattening,[],[f23])).
% 1.36/0.53  fof(f23,plain,(
% 1.36/0.53    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.36/0.53    inference(ennf_transformation,[],[f10])).
% 1.36/0.53  fof(f10,axiom,(
% 1.36/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.36/0.53  fof(f50,plain,(
% 1.36/0.53    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f222,plain,(
% 1.36/0.53    k1_xboole_0 = sK0 | ~v5_relat_1(sK1,sK0)),
% 1.36/0.53    inference(resolution,[],[f200,f100])).
% 1.36/0.53  fof(f200,plain,(
% 1.36/0.53    ( ! [X0] : (~v2_funct_2(sK1,X0) | k1_xboole_0 = sK0 | ~v5_relat_1(sK1,X0)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f199,f163])).
% 1.36/0.53  fof(f163,plain,(
% 1.36/0.53    ( ! [X2] : (~v2_funct_2(sK1,X2) | sK0 = X2 | ~v5_relat_1(sK1,X2)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f162,f79])).
% 1.36/0.53  fof(f162,plain,(
% 1.36/0.53    ( ! [X2] : (sK0 = X2 | ~v1_relat_1(sK1) | ~v2_funct_2(sK1,X2) | ~v5_relat_1(sK1,X2)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f159,f81])).
% 1.36/0.53  fof(f159,plain,(
% 1.36/0.53    ( ! [X2] : (sK0 = X2 | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~v2_funct_2(sK1,X2) | ~v5_relat_1(sK1,X2)) )),
% 1.36/0.53    inference(resolution,[],[f90,f100])).
% 1.36/0.53  fof(f90,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (~v2_funct_2(X0,X2) | X1 = X2 | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v2_funct_2(X0,X1) | ~v5_relat_1(X0,X1)) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f85])).
% 1.36/0.53  fof(f85,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (X1 = X2 | ~v2_funct_2(X0,X2) | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v2_funct_2(X0,X1) | ~v5_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(superposition,[],[f56,f56])).
% 1.36/0.53  fof(f199,plain,(
% 1.36/0.53    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = sK0 | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f198,f79])).
% 1.36/0.53  fof(f198,plain,(
% 1.36/0.53    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = sK0 | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1)) )),
% 1.36/0.53    inference(superposition,[],[f196,f56])).
% 1.36/0.53  fof(f196,plain,(
% 1.36/0.53    sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0),
% 1.36/0.53    inference(subsumption_resolution,[],[f195,f84])).
% 1.36/0.53  fof(f84,plain,(
% 1.36/0.53    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.36/0.53    inference(resolution,[],[f72,f48])).
% 1.36/0.53  fof(f195,plain,(
% 1.36/0.53    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0 | sK0 != k2_relat_1(sK1)),
% 1.36/0.53    inference(superposition,[],[f110,f128])).
% 1.36/0.53  fof(f128,plain,(
% 1.36/0.53    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relat_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f127,f44])).
% 1.36/0.53  fof(f127,plain,(
% 1.36/0.53    sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.36/0.53    inference(superposition,[],[f126,f60])).
% 1.36/0.53  fof(f60,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f26])).
% 1.36/0.53  fof(f26,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(ennf_transformation,[],[f6])).
% 1.36/0.53  fof(f6,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.53  fof(f126,plain,(
% 1.36/0.53    sK0 != k2_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f125,f41])).
% 1.36/0.53  fof(f125,plain,(
% 1.36/0.53    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f124,f42])).
% 1.36/0.53  fof(f124,plain,(
% 1.36/0.53    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f123,f44])).
% 1.36/0.53  fof(f123,plain,(
% 1.36/0.53    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f122,f45])).
% 1.36/0.53  fof(f122,plain,(
% 1.36/0.53    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f121,f46])).
% 1.36/0.53  fof(f46,plain,(
% 1.36/0.53    v1_funct_2(sK2,sK0,sK0)),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f121,plain,(
% 1.36/0.53    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f120,f48])).
% 1.36/0.53  fof(f120,plain,(
% 1.36/0.53    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f118])).
% 1.36/0.53  fof(f118,plain,(
% 1.36/0.53    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.36/0.53    inference(resolution,[],[f77,f73])).
% 1.36/0.53  fof(f73,plain,(
% 1.36/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 1.36/0.53    inference(forward_demodulation,[],[f49,f52])).
% 1.36/0.53  fof(f52,plain,(
% 1.36/0.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f11])).
% 1.36/0.53  fof(f11,axiom,(
% 1.36/0.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.36/0.53  fof(f49,plain,(
% 1.36/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f77,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f76,f75])).
% 1.36/0.53  fof(f75,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.53    inference(forward_demodulation,[],[f65,f52])).
% 1.36/0.53  fof(f65,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f31])).
% 1.36/0.53  fof(f31,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.53    inference(flattening,[],[f30])).
% 1.36/0.53  fof(f30,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.53    inference(ennf_transformation,[],[f12])).
% 1.36/0.53  fof(f12,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.36/0.53  fof(f76,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.53    inference(forward_demodulation,[],[f67,f52])).
% 1.36/0.53  fof(f67,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f33])).
% 1.36/0.53  fof(f33,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.53    inference(flattening,[],[f32])).
% 1.36/0.53  fof(f32,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.53    inference(ennf_transformation,[],[f13])).
% 1.36/0.53  fof(f13,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.36/0.53  % SZS output end Proof for theBenchmark
% 1.36/0.53  % (9893)------------------------------
% 1.36/0.53  % (9893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (9893)Termination reason: Refutation
% 1.36/0.53  
% 1.36/0.53  % (9893)Memory used [KB]: 1791
% 1.36/0.53  % (9893)Time elapsed: 0.120 s
% 1.36/0.53  % (9893)------------------------------
% 1.36/0.53  % (9893)------------------------------
% 1.36/0.53  % (9907)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.54  % (9888)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.54  % (9883)Success in time 0.171 s
%------------------------------------------------------------------------------
