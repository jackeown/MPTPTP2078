%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:51 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 745 expanded)
%              Number of leaves         :   25 ( 229 expanded)
%              Depth                    :   25
%              Number of atoms          :  496 (6439 expanded)
%              Number of equality atoms :  145 (2144 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f183,f1454])).

fof(f1454,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f1453])).

fof(f1453,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f1451,f68])).

fof(f68,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f53,f52])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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

fof(f1451,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f461,f1450])).

fof(f1450,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1449,f1137])).

fof(f1137,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(backward_demodulation,[],[f132,f1136])).

fof(f1136,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1135,f218])).

fof(f218,plain,(
    sK1 = k9_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f153,f216])).

fof(f216,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f213,f63])).

fof(f63,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f213,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f90,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f153,plain,(
    k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[],[f141,f151])).

fof(f151,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f146,f110])).

fof(f110,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f107,f83])).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f107,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f76,f59])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f146,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f89,f120])).

fof(f120,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f91,f59])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f141,plain,(
    ! [X7] : k2_relat_1(k7_relat_1(sK2,X7)) = k9_relat_1(sK2,X7) ),
    inference(resolution,[],[f84,f110])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1135,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f1134,f758])).

fof(f758,plain,(
    sK0 = k10_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f755,f100])).

fof(f100,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f69])).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f755,plain,(
    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f379,f736])).

fof(f736,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f727,f735])).

fof(f735,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f721,f285])).

fof(f285,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f93,f98])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f70,f69])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f721,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f64,f593])).

fof(f593,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f589,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f589,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f293,f59])).

fof(f293,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f290,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f290,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f727,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f726,f57])).

fof(f726,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f725,f59])).

fof(f725,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f724,f60])).

fof(f724,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f722,f62])).

fof(f722,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f97,f593])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f379,plain,(
    k1_relat_1(k5_relat_1(sK2,sK3)) = k10_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f210,f110])).

fof(f210,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k1_relat_1(k5_relat_1(X9,sK3)) = k10_relat_1(X9,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f74,f111])).

fof(f111,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f108,f83])).

fof(f108,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f76,f62])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1134,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f1116,f111])).

fof(f1116,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f710,f121])).

fof(f121,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f91,f62])).

fof(f710,plain,(
    ! [X17] :
      ( ~ v4_relat_1(X17,sK1)
      | k1_relat_1(X17) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X17)))
      | ~ v1_relat_1(X17) ) ),
    inference(subsumption_resolution,[],[f709,f110])).

fof(f709,plain,(
    ! [X17] :
      ( ~ v4_relat_1(X17,sK1)
      | ~ v1_relat_1(sK2)
      | k1_relat_1(X17) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X17)))
      | ~ v1_relat_1(X17) ) ),
    inference(subsumption_resolution,[],[f699,f57])).

fof(f699,plain,(
    ! [X17] :
      ( ~ v4_relat_1(X17,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k1_relat_1(X17) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X17)))
      | ~ v1_relat_1(X17) ) ),
    inference(superposition,[],[f248,f216])).

fof(f248,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X1) = k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f88,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f132,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f101,f111])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f73,f69])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1449,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1444,f237])).

fof(f237,plain,(
    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f236,f216])).

fof(f236,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f235,f110])).

fof(f235,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f234,f57])).

fof(f234,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f102,f65])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f82,f69])).

fof(f82,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1444,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f1323,f165])).

fof(f165,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_1
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1323,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f1321,f736])).

fof(f1321,plain,(
    ! [X18] :
      ( k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X18) ) ),
    inference(resolution,[],[f276,f110])).

fof(f276,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X14,X15),sK3) = k5_relat_1(X14,k5_relat_1(X15,sK3))
      | ~ v1_relat_1(X14) ) ),
    inference(resolution,[],[f75,f111])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f461,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f460,f120])).

fof(f460,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f458,f110])).

fof(f458,plain,
    ( ! [X0] :
        ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0))
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f199,f86])).

fof(f199,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_relat_1(sK2),X6)
        | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X6)) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f197,f165])).

fof(f197,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(sK2),X6)
      | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X6))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f104,f189])).

fof(f189,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f188,f110])).

fof(f188,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f187,f57])).

fof(f187,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f80,f65])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f85,f69])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f183,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f181,f110])).

fof(f181,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f180,f57])).

fof(f180,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f166,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f166,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (20393)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (20409)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (20408)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (20400)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (20401)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (20392)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (20390)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (20389)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (20387)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (20388)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (20391)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (20398)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (20414)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (20386)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (20413)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (20412)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (20394)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (20407)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (20395)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (20404)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (20415)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (20403)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (20406)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (20410)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (20405)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (20397)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (20396)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (20399)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (20402)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (20402)Refutation not found, incomplete strategy% (20402)------------------------------
% 0.20/0.55  % (20402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20402)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20402)Memory used [KB]: 10746
% 0.20/0.55  % (20402)Time elapsed: 0.150 s
% 0.20/0.55  % (20402)------------------------------
% 0.20/0.55  % (20402)------------------------------
% 0.20/0.56  % (20411)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.86/0.60  % (20392)Refutation found. Thanks to Tanya!
% 1.86/0.60  % SZS status Theorem for theBenchmark
% 1.86/0.60  % SZS output start Proof for theBenchmark
% 1.86/0.60  fof(f1456,plain,(
% 1.86/0.60    $false),
% 1.86/0.60    inference(avatar_sat_refutation,[],[f183,f1454])).
% 1.86/0.60  fof(f1454,plain,(
% 1.86/0.60    ~spl4_1),
% 1.86/0.60    inference(avatar_contradiction_clause,[],[f1453])).
% 1.86/0.60  fof(f1453,plain,(
% 1.86/0.60    $false | ~spl4_1),
% 1.86/0.60    inference(subsumption_resolution,[],[f1451,f68])).
% 1.86/0.60  fof(f68,plain,(
% 1.86/0.60    k2_funct_1(sK2) != sK3),
% 1.86/0.60    inference(cnf_transformation,[],[f54])).
% 1.86/0.60  fof(f54,plain,(
% 1.86/0.60    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.86/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f53,f52])).
% 1.86/0.60  fof(f52,plain,(
% 1.86/0.60    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.86/0.60    introduced(choice_axiom,[])).
% 1.86/0.60  fof(f53,plain,(
% 1.86/0.60    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.86/0.60    introduced(choice_axiom,[])).
% 1.86/0.60  fof(f25,plain,(
% 1.86/0.60    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.86/0.60    inference(flattening,[],[f24])).
% 1.86/0.60  fof(f24,plain,(
% 1.86/0.60    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.86/0.60    inference(ennf_transformation,[],[f23])).
% 1.86/0.60  fof(f23,negated_conjecture,(
% 1.86/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.86/0.60    inference(negated_conjecture,[],[f22])).
% 1.86/0.60  fof(f22,conjecture,(
% 1.86/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.86/0.60  fof(f1451,plain,(
% 1.86/0.60    k2_funct_1(sK2) = sK3 | ~spl4_1),
% 1.86/0.60    inference(backward_demodulation,[],[f461,f1450])).
% 1.86/0.60  fof(f1450,plain,(
% 1.86/0.60    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_1),
% 1.86/0.60    inference(forward_demodulation,[],[f1449,f1137])).
% 1.86/0.60  fof(f1137,plain,(
% 1.86/0.60    sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.86/0.60    inference(backward_demodulation,[],[f132,f1136])).
% 1.86/0.60  fof(f1136,plain,(
% 1.86/0.60    sK1 = k1_relat_1(sK3)),
% 1.86/0.60    inference(forward_demodulation,[],[f1135,f218])).
% 1.86/0.60  fof(f218,plain,(
% 1.86/0.60    sK1 = k9_relat_1(sK2,sK0)),
% 1.86/0.60    inference(backward_demodulation,[],[f153,f216])).
% 1.86/0.60  fof(f216,plain,(
% 1.86/0.60    sK1 = k2_relat_1(sK2)),
% 1.86/0.60    inference(forward_demodulation,[],[f213,f63])).
% 1.86/0.60  fof(f63,plain,(
% 1.86/0.60    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.86/0.60    inference(cnf_transformation,[],[f54])).
% 1.86/0.60  fof(f213,plain,(
% 1.86/0.60    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.86/0.60    inference(resolution,[],[f90,f59])).
% 1.86/0.60  fof(f59,plain,(
% 1.86/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.86/0.60    inference(cnf_transformation,[],[f54])).
% 1.86/0.60  fof(f90,plain,(
% 1.86/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f44])).
% 1.86/0.60  fof(f44,plain,(
% 1.86/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.60    inference(ennf_transformation,[],[f16])).
% 1.86/0.60  fof(f16,axiom,(
% 1.86/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.86/0.60  fof(f153,plain,(
% 1.86/0.60    k9_relat_1(sK2,sK0) = k2_relat_1(sK2)),
% 1.86/0.60    inference(superposition,[],[f141,f151])).
% 1.86/0.60  fof(f151,plain,(
% 1.86/0.60    sK2 = k7_relat_1(sK2,sK0)),
% 1.86/0.60    inference(subsumption_resolution,[],[f146,f110])).
% 1.86/0.60  fof(f110,plain,(
% 1.86/0.60    v1_relat_1(sK2)),
% 1.86/0.60    inference(subsumption_resolution,[],[f107,f83])).
% 1.86/0.60  fof(f83,plain,(
% 1.86/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.86/0.60    inference(cnf_transformation,[],[f3])).
% 1.86/0.60  fof(f3,axiom,(
% 1.86/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.86/0.60  fof(f107,plain,(
% 1.86/0.60    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.86/0.60    inference(resolution,[],[f76,f59])).
% 1.86/0.60  fof(f76,plain,(
% 1.86/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f29])).
% 1.86/0.60  fof(f29,plain,(
% 1.86/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.86/0.60    inference(ennf_transformation,[],[f1])).
% 1.86/0.60  fof(f1,axiom,(
% 1.86/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.86/0.60  fof(f146,plain,(
% 1.86/0.60    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.86/0.60    inference(resolution,[],[f89,f120])).
% 1.86/0.60  fof(f120,plain,(
% 1.86/0.60    v4_relat_1(sK2,sK0)),
% 1.86/0.60    inference(resolution,[],[f91,f59])).
% 1.86/0.60  fof(f91,plain,(
% 1.86/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f45])).
% 1.86/0.60  fof(f45,plain,(
% 1.86/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.60    inference(ennf_transformation,[],[f15])).
% 1.86/0.60  fof(f15,axiom,(
% 1.86/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.86/0.60  fof(f89,plain,(
% 1.86/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f43])).
% 1.86/0.60  fof(f43,plain,(
% 1.86/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.86/0.60    inference(flattening,[],[f42])).
% 1.86/0.60  fof(f42,plain,(
% 1.86/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.86/0.60    inference(ennf_transformation,[],[f6])).
% 1.86/0.60  fof(f6,axiom,(
% 1.86/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.86/0.60  fof(f141,plain,(
% 1.86/0.60    ( ! [X7] : (k2_relat_1(k7_relat_1(sK2,X7)) = k9_relat_1(sK2,X7)) )),
% 1.86/0.60    inference(resolution,[],[f84,f110])).
% 1.86/0.60  fof(f84,plain,(
% 1.86/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f36])).
% 1.86/0.60  fof(f36,plain,(
% 1.86/0.60    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.86/0.60    inference(ennf_transformation,[],[f4])).
% 1.86/0.60  fof(f4,axiom,(
% 1.86/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.86/0.60  fof(f1135,plain,(
% 1.86/0.60    k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 1.86/0.60    inference(forward_demodulation,[],[f1134,f758])).
% 1.86/0.60  fof(f758,plain,(
% 1.86/0.60    sK0 = k10_relat_1(sK2,k1_relat_1(sK3))),
% 1.86/0.60    inference(forward_demodulation,[],[f755,f100])).
% 1.86/0.60  fof(f100,plain,(
% 1.86/0.60    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.86/0.60    inference(definition_unfolding,[],[f71,f69])).
% 1.86/0.60  fof(f69,plain,(
% 1.86/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f21])).
% 1.86/0.60  fof(f21,axiom,(
% 1.86/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.86/0.60  fof(f71,plain,(
% 1.86/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.86/0.60    inference(cnf_transformation,[],[f8])).
% 1.86/0.60  fof(f8,axiom,(
% 1.86/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.86/0.60  fof(f755,plain,(
% 1.86/0.60    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0))),
% 1.86/0.60    inference(backward_demodulation,[],[f379,f736])).
% 1.86/0.60  fof(f736,plain,(
% 1.86/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.86/0.60    inference(global_subsumption,[],[f727,f735])).
% 1.86/0.60  fof(f735,plain,(
% 1.86/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.86/0.60    inference(resolution,[],[f721,f285])).
% 1.86/0.60  fof(f285,plain,(
% 1.86/0.60    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.86/0.60    inference(resolution,[],[f93,f98])).
% 1.86/0.60  fof(f98,plain,(
% 1.86/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.86/0.60    inference(definition_unfolding,[],[f70,f69])).
% 1.86/0.60  fof(f70,plain,(
% 1.86/0.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.86/0.60    inference(cnf_transformation,[],[f18])).
% 1.86/0.60  fof(f18,axiom,(
% 1.86/0.60    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.86/0.60  fof(f93,plain,(
% 1.86/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.60    inference(cnf_transformation,[],[f56])).
% 1.86/0.60  fof(f56,plain,(
% 1.86/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.60    inference(nnf_transformation,[],[f47])).
% 1.86/0.60  fof(f47,plain,(
% 1.86/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.60    inference(flattening,[],[f46])).
% 1.86/0.60  fof(f46,plain,(
% 1.86/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.86/0.60    inference(ennf_transformation,[],[f17])).
% 1.86/0.60  fof(f17,axiom,(
% 1.86/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.86/0.60  fof(f721,plain,(
% 1.86/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.86/0.60    inference(backward_demodulation,[],[f64,f593])).
% 1.86/0.60  fof(f593,plain,(
% 1.86/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.86/0.60    inference(subsumption_resolution,[],[f589,f57])).
% 1.86/0.60  fof(f57,plain,(
% 1.86/0.60    v1_funct_1(sK2)),
% 1.86/0.60    inference(cnf_transformation,[],[f54])).
% 1.86/0.60  fof(f589,plain,(
% 1.86/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.86/0.60    inference(resolution,[],[f293,f59])).
% 1.86/0.60  fof(f293,plain,(
% 1.86/0.60    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 1.86/0.60    inference(subsumption_resolution,[],[f290,f60])).
% 1.86/0.60  fof(f60,plain,(
% 1.86/0.60    v1_funct_1(sK3)),
% 1.86/0.60    inference(cnf_transformation,[],[f54])).
% 1.86/0.60  fof(f290,plain,(
% 1.86/0.60    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.86/0.60    inference(resolution,[],[f95,f62])).
% 1.86/0.60  fof(f62,plain,(
% 1.86/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.86/0.60    inference(cnf_transformation,[],[f54])).
% 1.86/0.60  fof(f95,plain,(
% 1.86/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f49])).
% 1.86/0.60  fof(f49,plain,(
% 1.86/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.86/0.60    inference(flattening,[],[f48])).
% 1.86/0.60  fof(f48,plain,(
% 1.86/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.86/0.60    inference(ennf_transformation,[],[f20])).
% 1.86/0.60  fof(f20,axiom,(
% 1.86/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.86/0.60  fof(f64,plain,(
% 1.86/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.86/0.60    inference(cnf_transformation,[],[f54])).
% 1.86/0.60  fof(f727,plain,(
% 1.86/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.86/0.60    inference(subsumption_resolution,[],[f726,f57])).
% 1.86/0.60  fof(f726,plain,(
% 1.86/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.86/0.60    inference(subsumption_resolution,[],[f725,f59])).
% 1.86/0.60  fof(f725,plain,(
% 1.86/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.86/0.60    inference(subsumption_resolution,[],[f724,f60])).
% 1.86/0.60  fof(f724,plain,(
% 1.86/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.86/0.60    inference(subsumption_resolution,[],[f722,f62])).
% 1.86/0.60  fof(f722,plain,(
% 1.86/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.86/0.60    inference(superposition,[],[f97,f593])).
% 1.86/0.60  fof(f97,plain,(
% 1.86/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f51])).
% 1.86/0.60  fof(f51,plain,(
% 1.86/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.86/0.60    inference(flattening,[],[f50])).
% 1.86/0.60  fof(f50,plain,(
% 1.86/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.86/0.60    inference(ennf_transformation,[],[f19])).
% 1.86/0.60  fof(f19,axiom,(
% 1.86/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.86/0.60  fof(f379,plain,(
% 1.86/0.60    k1_relat_1(k5_relat_1(sK2,sK3)) = k10_relat_1(sK2,k1_relat_1(sK3))),
% 1.86/0.60    inference(resolution,[],[f210,f110])).
% 1.86/0.60  fof(f210,plain,(
% 1.86/0.60    ( ! [X9] : (~v1_relat_1(X9) | k1_relat_1(k5_relat_1(X9,sK3)) = k10_relat_1(X9,k1_relat_1(sK3))) )),
% 1.86/0.60    inference(resolution,[],[f74,f111])).
% 1.86/0.60  fof(f111,plain,(
% 1.86/0.60    v1_relat_1(sK3)),
% 1.86/0.60    inference(subsumption_resolution,[],[f108,f83])).
% 1.86/0.60  fof(f108,plain,(
% 1.86/0.60    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.86/0.60    inference(resolution,[],[f76,f62])).
% 1.86/0.60  fof(f74,plain,(
% 1.86/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f27])).
% 1.86/0.60  fof(f27,plain,(
% 1.86/0.60    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.86/0.60    inference(ennf_transformation,[],[f5])).
% 1.86/0.60  fof(f5,axiom,(
% 1.86/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.86/0.60  fof(f1134,plain,(
% 1.86/0.60    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))),
% 1.86/0.60    inference(subsumption_resolution,[],[f1116,f111])).
% 1.86/0.60  fof(f1116,plain,(
% 1.86/0.60    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) | ~v1_relat_1(sK3)),
% 1.86/0.60    inference(resolution,[],[f710,f121])).
% 1.86/0.60  fof(f121,plain,(
% 1.86/0.60    v4_relat_1(sK3,sK1)),
% 1.86/0.60    inference(resolution,[],[f91,f62])).
% 1.86/0.60  fof(f710,plain,(
% 1.86/0.60    ( ! [X17] : (~v4_relat_1(X17,sK1) | k1_relat_1(X17) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X17))) | ~v1_relat_1(X17)) )),
% 1.86/0.60    inference(subsumption_resolution,[],[f709,f110])).
% 1.86/0.60  fof(f709,plain,(
% 1.86/0.60    ( ! [X17] : (~v4_relat_1(X17,sK1) | ~v1_relat_1(sK2) | k1_relat_1(X17) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X17))) | ~v1_relat_1(X17)) )),
% 1.86/0.60    inference(subsumption_resolution,[],[f699,f57])).
% 1.86/0.60  fof(f699,plain,(
% 1.86/0.60    ( ! [X17] : (~v4_relat_1(X17,sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(X17) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X17))) | ~v1_relat_1(X17)) )),
% 1.86/0.60    inference(superposition,[],[f248,f216])).
% 1.86/0.60  fof(f248,plain,(
% 1.86/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X1) = k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.86/0.60    inference(resolution,[],[f88,f86])).
% 1.86/0.60  fof(f86,plain,(
% 1.86/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f55])).
% 1.86/0.60  fof(f55,plain,(
% 1.86/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.86/0.60    inference(nnf_transformation,[],[f39])).
% 1.86/0.60  fof(f39,plain,(
% 1.86/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.86/0.60    inference(ennf_transformation,[],[f2])).
% 1.86/0.60  fof(f2,axiom,(
% 1.86/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.86/0.60  fof(f88,plain,(
% 1.86/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f41])).
% 1.86/0.60  fof(f41,plain,(
% 1.86/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.86/0.60    inference(flattening,[],[f40])).
% 1.86/0.60  fof(f40,plain,(
% 1.86/0.60    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.86/0.60    inference(ennf_transformation,[],[f12])).
% 1.86/0.60  fof(f12,axiom,(
% 1.86/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.86/0.60  fof(f132,plain,(
% 1.86/0.60    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 1.86/0.60    inference(resolution,[],[f101,f111])).
% 1.86/0.60  fof(f101,plain,(
% 1.86/0.60    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.86/0.60    inference(definition_unfolding,[],[f73,f69])).
% 1.86/0.60  fof(f73,plain,(
% 1.86/0.60    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f26])).
% 1.86/0.60  fof(f26,plain,(
% 1.86/0.60    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.86/0.60    inference(ennf_transformation,[],[f9])).
% 1.86/0.60  fof(f9,axiom,(
% 1.86/0.60    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.86/0.60  fof(f1449,plain,(
% 1.86/0.60    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_1),
% 1.86/0.60    inference(forward_demodulation,[],[f1444,f237])).
% 1.86/0.60  fof(f237,plain,(
% 1.86/0.60    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.86/0.60    inference(forward_demodulation,[],[f236,f216])).
% 1.86/0.60  fof(f236,plain,(
% 1.86/0.60    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.86/0.60    inference(subsumption_resolution,[],[f235,f110])).
% 1.86/0.60  fof(f235,plain,(
% 1.86/0.60    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 1.86/0.60    inference(subsumption_resolution,[],[f234,f57])).
% 1.86/0.60  fof(f234,plain,(
% 1.86/0.60    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.86/0.60    inference(resolution,[],[f102,f65])).
% 1.86/0.60  fof(f65,plain,(
% 1.86/0.60    v2_funct_1(sK2)),
% 1.86/0.60    inference(cnf_transformation,[],[f54])).
% 1.86/0.60  fof(f102,plain,(
% 1.86/0.60    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.86/0.60    inference(definition_unfolding,[],[f82,f69])).
% 1.86/0.60  fof(f82,plain,(
% 1.86/0.60    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f35])).
% 1.86/0.60  fof(f35,plain,(
% 1.86/0.60    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.86/0.60    inference(flattening,[],[f34])).
% 1.86/0.61  fof(f34,plain,(
% 1.86/0.61    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.86/0.61    inference(ennf_transformation,[],[f14])).
% 1.86/0.61  fof(f14,axiom,(
% 1.86/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 1.86/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.86/0.61  fof(f1444,plain,(
% 1.86/0.61    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | ~spl4_1),
% 1.86/0.61    inference(resolution,[],[f1323,f165])).
% 1.86/0.61  fof(f165,plain,(
% 1.86/0.61    v1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.86/0.61    inference(avatar_component_clause,[],[f164])).
% 1.86/0.61  fof(f164,plain,(
% 1.86/0.61    spl4_1 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.86/0.61  fof(f1323,plain,(
% 1.86/0.61    ( ! [X18] : (~v1_relat_1(X18) | k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k6_partfun1(sK0))) )),
% 1.86/0.61    inference(forward_demodulation,[],[f1321,f736])).
% 1.86/0.61  fof(f1321,plain,(
% 1.86/0.61    ( ! [X18] : (k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X18)) )),
% 1.86/0.61    inference(resolution,[],[f276,f110])).
% 1.86/0.61  fof(f276,plain,(
% 1.86/0.61    ( ! [X14,X15] : (~v1_relat_1(X15) | k5_relat_1(k5_relat_1(X14,X15),sK3) = k5_relat_1(X14,k5_relat_1(X15,sK3)) | ~v1_relat_1(X14)) )),
% 1.86/0.61    inference(resolution,[],[f75,f111])).
% 1.86/0.61  fof(f75,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f28])).
% 1.86/0.61  fof(f28,plain,(
% 1.86/0.61    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.86/0.61    inference(ennf_transformation,[],[f7])).
% 1.86/0.61  fof(f7,axiom,(
% 1.86/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.86/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.86/0.61  fof(f461,plain,(
% 1.86/0.61    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_1),
% 1.86/0.61    inference(resolution,[],[f460,f120])).
% 1.86/0.61  fof(f460,plain,(
% 1.86/0.61    ( ! [X0] : (~v4_relat_1(sK2,X0) | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0))) ) | ~spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f458,f110])).
% 1.86/0.61  fof(f458,plain,(
% 1.86/0.61    ( ! [X0] : (k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl4_1),
% 1.86/0.61    inference(resolution,[],[f199,f86])).
% 1.86/0.61  fof(f199,plain,(
% 1.86/0.61    ( ! [X6] : (~r1_tarski(k1_relat_1(sK2),X6) | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X6))) ) | ~spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f197,f165])).
% 1.86/0.61  fof(f197,plain,(
% 1.86/0.61    ( ! [X6] : (~r1_tarski(k1_relat_1(sK2),X6) | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X6)) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 1.86/0.61    inference(superposition,[],[f104,f189])).
% 1.86/0.61  fof(f189,plain,(
% 1.86/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.86/0.61    inference(subsumption_resolution,[],[f188,f110])).
% 1.86/0.61  fof(f188,plain,(
% 1.86/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.86/0.61    inference(subsumption_resolution,[],[f187,f57])).
% 1.86/0.61  fof(f187,plain,(
% 1.86/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.86/0.61    inference(resolution,[],[f80,f65])).
% 1.86/0.61  fof(f80,plain,(
% 1.86/0.61    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f33])).
% 1.86/0.61  fof(f33,plain,(
% 1.86/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.86/0.61    inference(flattening,[],[f32])).
% 1.86/0.61  fof(f32,plain,(
% 1.86/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.86/0.61    inference(ennf_transformation,[],[f13])).
% 1.86/0.61  fof(f13,axiom,(
% 1.86/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.86/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.86/0.61  fof(f104,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 1.86/0.61    inference(definition_unfolding,[],[f85,f69])).
% 1.86/0.61  fof(f85,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f38])).
% 1.86/0.61  fof(f38,plain,(
% 1.86/0.61    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.86/0.61    inference(flattening,[],[f37])).
% 1.86/0.61  fof(f37,plain,(
% 1.86/0.61    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.86/0.61    inference(ennf_transformation,[],[f10])).
% 1.86/0.61  fof(f10,axiom,(
% 1.86/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.86/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.86/0.61  fof(f183,plain,(
% 1.86/0.61    spl4_1),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f182])).
% 1.86/0.61  fof(f182,plain,(
% 1.86/0.61    $false | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f181,f110])).
% 1.86/0.61  fof(f181,plain,(
% 1.86/0.61    ~v1_relat_1(sK2) | spl4_1),
% 1.86/0.61    inference(subsumption_resolution,[],[f180,f57])).
% 1.86/0.61  fof(f180,plain,(
% 1.86/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 1.86/0.61    inference(resolution,[],[f166,f77])).
% 1.86/0.61  fof(f77,plain,(
% 1.86/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f31])).
% 1.86/0.61  fof(f31,plain,(
% 1.86/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.86/0.61    inference(flattening,[],[f30])).
% 1.86/0.61  fof(f30,plain,(
% 1.86/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.86/0.61    inference(ennf_transformation,[],[f11])).
% 1.86/0.61  fof(f11,axiom,(
% 1.86/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.86/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.86/0.61  fof(f166,plain,(
% 1.86/0.61    ~v1_relat_1(k2_funct_1(sK2)) | spl4_1),
% 1.86/0.61    inference(avatar_component_clause,[],[f164])).
% 1.86/0.61  % SZS output end Proof for theBenchmark
% 1.86/0.61  % (20392)------------------------------
% 1.86/0.61  % (20392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.61  % (20392)Termination reason: Refutation
% 1.86/0.61  
% 1.86/0.61  % (20392)Memory used [KB]: 12025
% 1.86/0.61  % (20392)Time elapsed: 0.149 s
% 1.86/0.61  % (20392)------------------------------
% 1.86/0.61  % (20392)------------------------------
% 1.86/0.61  % (20385)Success in time 0.248 s
%------------------------------------------------------------------------------
