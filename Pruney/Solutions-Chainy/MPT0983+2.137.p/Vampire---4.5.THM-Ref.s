%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:55 EST 2020

% Result     : Theorem 2.94s
% Output     : Refutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  135 (1346 expanded)
%              Number of leaves         :   22 ( 414 expanded)
%              Depth                    :   25
%              Number of atoms          :  433 (9751 expanded)
%              Number of equality atoms :   65 ( 278 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2584,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2355,f823])).

fof(f823,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f84,f367])).

fof(f367,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f253,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f253,plain,(
    v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f167,f79])).

fof(f79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f167,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f100,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f2355,plain,(
    ~ v2_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1440,f2258])).

fof(f2258,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1598,f89])).

fof(f1598,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f1478,f79])).

fof(f1478,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(backward_demodulation,[],[f171,f1467])).

fof(f1467,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1440,f1333])).

fof(f1333,plain,
    ( v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f1306,f84])).

fof(f1306,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f640,f1291])).

fof(f1291,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f720,f643])).

fof(f643,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f641,f636])).

fof(f636,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f340,f76])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f54,f53])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) ) ),
    inference(resolution,[],[f232,f73])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f232,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f213,f71])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f213,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f120,f74])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f641,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f205,f636])).

fof(f205,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f204,f82])).

fof(f204,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f118,f133])).

fof(f133,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f77,f81])).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f720,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f717,f636])).

fof(f717,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f357,f76])).

fof(f357,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f242,f73])).

fof(f242,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f215,f71])).

fof(f215,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f122,f74])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f640,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f239,f636])).

fof(f239,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f238,f71])).

fof(f238,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f237,f73])).

fof(f237,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f221,f72])).

fof(f72,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f221,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,X2,sK1)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | k1_xboole_0 = sK0
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f220,f74])).

fof(f220,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(X3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f217,f76])).

fof(f217,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v2_funct_1(X3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f116,f75])).

fof(f75,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f171,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f101,f73])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f1440,plain,(
    ~ v2_funct_1(sK2) ),
    inference(resolution,[],[f1376,f78])).

fof(f78,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f1376,plain,(
    v2_funct_2(sK3,sK0) ),
    inference(backward_demodulation,[],[f617,f1361])).

fof(f1361,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1360,f309])).

fof(f309,plain,(
    r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(resolution,[],[f264,f201])).

fof(f201,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(resolution,[],[f161,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f161,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f115,f76])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f264,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f152,f76])).

fof(f152,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f88,f96])).

fof(f96,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1360,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1359,f86])).

fof(f86,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1359,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_relat_1(sK0)))
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1358,f1291])).

fof(f1358,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(forward_demodulation,[],[f1330,f86])).

fof(f1330,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(backward_demodulation,[],[f1250,f1291])).

fof(f1250,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k5_relat_1(sK2,sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(resolution,[],[f588,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f588,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) ),
    inference(resolution,[],[f316,f263])).

fof(f263,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f152,f73])).

fof(f316,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | r1_tarski(k2_relat_1(k5_relat_1(X3,sK3)),k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f264,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f617,plain,(
    v2_funct_2(sK3,k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f615,f264])).

fof(f615,plain,
    ( v2_funct_2(sK3,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f576,f123])).

fof(f123,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f576,plain,(
    v5_relat_1(sK3,k2_relat_1(sK3)) ),
    inference(resolution,[],[f317,f124])).

fof(f124,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f317,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relat_1(sK3),X4)
      | v5_relat_1(sK3,X4) ) ),
    inference(resolution,[],[f264,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:37:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (21503)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (21511)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (21496)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.56  % (21504)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.57  % (21512)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.62/0.59  % (21492)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.62/0.60  % (21505)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.62/0.60  % (21500)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.62/0.60  % (21494)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.62/0.60  % (21499)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.62/0.61  % (21508)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.62/0.61  % (21497)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.62/0.61  % (21507)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.62/0.61  % (21489)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.62/0.61  % (21509)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.62/0.61  % (21516)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.62/0.61  % (21515)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.62/0.62  % (21517)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.62/0.62  % (21491)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.62/0.62  % (21513)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.62/0.62  % (21501)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.62/0.62  % (21505)Refutation not found, incomplete strategy% (21505)------------------------------
% 1.62/0.62  % (21505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.62  % (21505)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.62  
% 1.62/0.62  % (21505)Memory used [KB]: 10746
% 1.62/0.62  % (21505)Time elapsed: 0.189 s
% 1.62/0.62  % (21505)------------------------------
% 1.62/0.62  % (21505)------------------------------
% 1.62/0.63  % (21499)Refutation not found, incomplete strategy% (21499)------------------------------
% 1.62/0.63  % (21499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.63  % (21499)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.63  
% 1.62/0.63  % (21499)Memory used [KB]: 10874
% 1.62/0.63  % (21499)Time elapsed: 0.190 s
% 1.62/0.63  % (21499)------------------------------
% 1.62/0.63  % (21499)------------------------------
% 1.62/0.63  % (21518)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.62/0.63  % (21495)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.64  % (21502)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.62/0.64  % (21517)Refutation not found, incomplete strategy% (21517)------------------------------
% 1.62/0.64  % (21517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.64  % (21517)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.64  
% 1.62/0.64  % (21517)Memory used [KB]: 11001
% 1.62/0.64  % (21517)Time elapsed: 0.210 s
% 1.62/0.64  % (21517)------------------------------
% 1.62/0.64  % (21517)------------------------------
% 2.09/0.65  % (21510)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.09/0.65  % (21493)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 2.09/0.66  % (21514)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.09/0.67  % (21498)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.35/0.67  % (21506)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.35/0.69  % (21490)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 2.94/0.77  % (21496)Refutation found. Thanks to Tanya!
% 2.94/0.77  % SZS status Theorem for theBenchmark
% 2.94/0.77  % SZS output start Proof for theBenchmark
% 2.94/0.77  fof(f2584,plain,(
% 2.94/0.77    $false),
% 2.94/0.77    inference(subsumption_resolution,[],[f2355,f823])).
% 2.94/0.77  fof(f823,plain,(
% 2.94/0.77    v2_funct_1(k1_xboole_0)),
% 2.94/0.77    inference(superposition,[],[f84,f367])).
% 2.94/0.77  fof(f367,plain,(
% 2.94/0.77    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.94/0.77    inference(resolution,[],[f253,f89])).
% 2.94/0.77  fof(f89,plain,(
% 2.94/0.77    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.94/0.77    inference(cnf_transformation,[],[f34])).
% 2.94/0.77  fof(f34,plain,(
% 2.94/0.77    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.94/0.77    inference(ennf_transformation,[],[f2])).
% 2.94/0.77  fof(f2,axiom,(
% 2.94/0.77    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.94/0.77  fof(f253,plain,(
% 2.94/0.77    v1_xboole_0(k6_relat_1(k1_xboole_0))),
% 2.94/0.77    inference(resolution,[],[f167,f79])).
% 2.94/0.77  fof(f79,plain,(
% 2.94/0.77    v1_xboole_0(k1_xboole_0)),
% 2.94/0.77    inference(cnf_transformation,[],[f1])).
% 2.94/0.77  fof(f1,axiom,(
% 2.94/0.77    v1_xboole_0(k1_xboole_0)),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.94/0.77  fof(f167,plain,(
% 2.94/0.77    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k6_relat_1(X0))) )),
% 2.94/0.77    inference(resolution,[],[f100,f82])).
% 2.94/0.77  fof(f82,plain,(
% 2.94/0.77    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f21])).
% 2.94/0.77  fof(f21,axiom,(
% 2.94/0.77    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.94/0.77  fof(f100,plain,(
% 2.94/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f39])).
% 2.94/0.77  fof(f39,plain,(
% 2.94/0.77    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.94/0.77    inference(ennf_transformation,[],[f19])).
% 2.94/0.77  fof(f19,axiom,(
% 2.94/0.77    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 2.94/0.77  fof(f84,plain,(
% 2.94/0.77    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f16])).
% 2.94/0.77  fof(f16,axiom,(
% 2.94/0.77    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.94/0.77  fof(f2355,plain,(
% 2.94/0.77    ~v2_funct_1(k1_xboole_0)),
% 2.94/0.77    inference(backward_demodulation,[],[f1440,f2258])).
% 2.94/0.77  fof(f2258,plain,(
% 2.94/0.77    k1_xboole_0 = sK2),
% 2.94/0.77    inference(resolution,[],[f1598,f89])).
% 2.94/0.77  fof(f1598,plain,(
% 2.94/0.77    v1_xboole_0(sK2)),
% 2.94/0.77    inference(subsumption_resolution,[],[f1478,f79])).
% 2.94/0.77  fof(f1478,plain,(
% 2.94/0.77    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2)),
% 2.94/0.77    inference(backward_demodulation,[],[f171,f1467])).
% 2.94/0.77  fof(f1467,plain,(
% 2.94/0.77    k1_xboole_0 = sK0),
% 2.94/0.77    inference(resolution,[],[f1440,f1333])).
% 2.94/0.77  fof(f1333,plain,(
% 2.94/0.77    v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 2.94/0.77    inference(subsumption_resolution,[],[f1306,f84])).
% 2.94/0.77  fof(f1306,plain,(
% 2.94/0.77    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 2.94/0.77    inference(backward_demodulation,[],[f640,f1291])).
% 2.94/0.77  fof(f1291,plain,(
% 2.94/0.77    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.94/0.77    inference(resolution,[],[f720,f643])).
% 2.94/0.77  fof(f643,plain,(
% 2.94/0.77    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.94/0.77    inference(forward_demodulation,[],[f641,f636])).
% 2.94/0.77  fof(f636,plain,(
% 2.94/0.77    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.94/0.77    inference(resolution,[],[f340,f76])).
% 2.94/0.77  fof(f76,plain,(
% 2.94/0.77    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.94/0.77    inference(cnf_transformation,[],[f55])).
% 2.94/0.77  fof(f55,plain,(
% 2.94/0.77    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.94/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f54,f53])).
% 2.94/0.77  fof(f53,plain,(
% 2.94/0.77    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.94/0.77    introduced(choice_axiom,[])).
% 2.94/0.77  fof(f54,plain,(
% 2.94/0.77    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.94/0.77    introduced(choice_axiom,[])).
% 2.94/0.77  fof(f31,plain,(
% 2.94/0.77    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.94/0.77    inference(flattening,[],[f30])).
% 2.94/0.77  fof(f30,plain,(
% 2.94/0.77    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.94/0.77    inference(ennf_transformation,[],[f28])).
% 2.94/0.77  fof(f28,negated_conjecture,(
% 2.94/0.77    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.94/0.77    inference(negated_conjecture,[],[f27])).
% 2.94/0.77  fof(f27,conjecture,(
% 2.94/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 2.94/0.77  fof(f340,plain,(
% 2.94/0.77    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3)) )),
% 2.94/0.77    inference(resolution,[],[f232,f73])).
% 2.94/0.77  fof(f73,plain,(
% 2.94/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.94/0.77    inference(cnf_transformation,[],[f55])).
% 2.94/0.77  fof(f232,plain,(
% 2.94/0.77    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.94/0.77    inference(resolution,[],[f213,f71])).
% 2.94/0.77  fof(f71,plain,(
% 2.94/0.77    v1_funct_1(sK2)),
% 2.94/0.77    inference(cnf_transformation,[],[f55])).
% 2.94/0.77  fof(f213,plain,(
% 2.94/0.77    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 2.94/0.77    inference(resolution,[],[f120,f74])).
% 2.94/0.77  fof(f74,plain,(
% 2.94/0.77    v1_funct_1(sK3)),
% 2.94/0.77    inference(cnf_transformation,[],[f55])).
% 2.94/0.77  fof(f120,plain,(
% 2.94/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f50])).
% 2.94/0.77  fof(f50,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.94/0.77    inference(flattening,[],[f49])).
% 2.94/0.77  fof(f49,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.94/0.77    inference(ennf_transformation,[],[f24])).
% 2.94/0.77  fof(f24,axiom,(
% 2.94/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.94/0.77  fof(f641,plain,(
% 2.94/0.77    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.94/0.77    inference(backward_demodulation,[],[f205,f636])).
% 2.94/0.77  fof(f205,plain,(
% 2.94/0.77    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.94/0.77    inference(subsumption_resolution,[],[f204,f82])).
% 2.94/0.77  fof(f204,plain,(
% 2.94/0.77    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.94/0.77    inference(resolution,[],[f118,f133])).
% 2.94/0.77  fof(f133,plain,(
% 2.94/0.77    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.94/0.77    inference(forward_demodulation,[],[f77,f81])).
% 2.94/0.77  fof(f81,plain,(
% 2.94/0.77    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f25])).
% 2.94/0.77  fof(f25,axiom,(
% 2.94/0.77    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.94/0.77  fof(f77,plain,(
% 2.94/0.77    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.94/0.77    inference(cnf_transformation,[],[f55])).
% 2.94/0.77  fof(f118,plain,(
% 2.94/0.77    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f70])).
% 2.94/0.77  fof(f70,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.77    inference(nnf_transformation,[],[f48])).
% 2.94/0.77  fof(f48,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.77    inference(flattening,[],[f47])).
% 2.94/0.77  fof(f47,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.94/0.77    inference(ennf_transformation,[],[f20])).
% 2.94/0.77  fof(f20,axiom,(
% 2.94/0.77    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.94/0.77  fof(f720,plain,(
% 2.94/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.94/0.77    inference(forward_demodulation,[],[f717,f636])).
% 2.94/0.77  fof(f717,plain,(
% 2.94/0.77    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.94/0.77    inference(resolution,[],[f357,f76])).
% 2.94/0.77  fof(f357,plain,(
% 2.94/0.77    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 2.94/0.77    inference(resolution,[],[f242,f73])).
% 2.94/0.77  fof(f242,plain,(
% 2.94/0.77    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.94/0.77    inference(resolution,[],[f215,f71])).
% 2.94/0.77  fof(f215,plain,(
% 2.94/0.77    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 2.94/0.77    inference(resolution,[],[f122,f74])).
% 2.94/0.77  fof(f122,plain,(
% 2.94/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f52])).
% 2.94/0.77  fof(f52,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.94/0.77    inference(flattening,[],[f51])).
% 2.94/0.77  fof(f51,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.94/0.77    inference(ennf_transformation,[],[f23])).
% 2.94/0.77  fof(f23,axiom,(
% 2.94/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.94/0.77  fof(f640,plain,(
% 2.94/0.77    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 2.94/0.77    inference(backward_demodulation,[],[f239,f636])).
% 2.94/0.77  fof(f239,plain,(
% 2.94/0.77    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 2.94/0.77    inference(subsumption_resolution,[],[f238,f71])).
% 2.94/0.77  fof(f238,plain,(
% 2.94/0.77    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK2) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 2.94/0.77    inference(subsumption_resolution,[],[f237,f73])).
% 2.94/0.77  fof(f237,plain,(
% 2.94/0.77    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 2.94/0.77    inference(resolution,[],[f221,f72])).
% 2.94/0.77  fof(f72,plain,(
% 2.94/0.77    v1_funct_2(sK2,sK0,sK1)),
% 2.94/0.77    inference(cnf_transformation,[],[f55])).
% 2.94/0.77  fof(f221,plain,(
% 2.94/0.77    ( ! [X2,X3] : (~v1_funct_2(X3,X2,sK1) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | k1_xboole_0 = sK0 | ~v1_funct_1(X3)) )),
% 2.94/0.77    inference(subsumption_resolution,[],[f220,f74])).
% 2.94/0.77  fof(f220,plain,(
% 2.94/0.77    ( ! [X2,X3] : (k1_xboole_0 = sK0 | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(X3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 2.94/0.77    inference(subsumption_resolution,[],[f217,f76])).
% 2.94/0.77  fof(f217,plain,(
% 2.94/0.77    ( ! [X2,X3] : (k1_xboole_0 = sK0 | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v2_funct_1(X3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 2.94/0.77    inference(resolution,[],[f116,f75])).
% 2.94/0.77  fof(f75,plain,(
% 2.94/0.77    v1_funct_2(sK3,sK1,sK0)),
% 2.94/0.77    inference(cnf_transformation,[],[f55])).
% 2.94/0.77  fof(f116,plain,(
% 2.94/0.77    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,X1,X2) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f46])).
% 2.94/0.77  fof(f46,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.94/0.77    inference(flattening,[],[f45])).
% 2.94/0.77  fof(f45,plain,(
% 2.94/0.77    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.94/0.77    inference(ennf_transformation,[],[f26])).
% 2.94/0.77  fof(f26,axiom,(
% 2.94/0.77    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 2.94/0.77  fof(f171,plain,(
% 2.94/0.77    ~v1_xboole_0(sK0) | v1_xboole_0(sK2)),
% 2.94/0.77    inference(resolution,[],[f101,f73])).
% 2.94/0.77  fof(f101,plain,(
% 2.94/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f40])).
% 2.94/0.77  fof(f40,plain,(
% 2.94/0.77    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.94/0.77    inference(ennf_transformation,[],[f18])).
% 2.94/0.77  fof(f18,axiom,(
% 2.94/0.77    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 2.94/0.77  fof(f1440,plain,(
% 2.94/0.77    ~v2_funct_1(sK2)),
% 2.94/0.77    inference(resolution,[],[f1376,f78])).
% 2.94/0.77  fof(f78,plain,(
% 2.94/0.77    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.94/0.77    inference(cnf_transformation,[],[f55])).
% 2.94/0.77  fof(f1376,plain,(
% 2.94/0.77    v2_funct_2(sK3,sK0)),
% 2.94/0.77    inference(backward_demodulation,[],[f617,f1361])).
% 2.94/0.77  fof(f1361,plain,(
% 2.94/0.77    sK0 = k2_relat_1(sK3)),
% 2.94/0.77    inference(subsumption_resolution,[],[f1360,f309])).
% 2.94/0.77  fof(f309,plain,(
% 2.94/0.77    r1_tarski(k2_relat_1(sK3),sK0)),
% 2.94/0.77    inference(resolution,[],[f264,f201])).
% 2.94/0.77  fof(f201,plain,(
% 2.94/0.77    ~v1_relat_1(sK3) | r1_tarski(k2_relat_1(sK3),sK0)),
% 2.94/0.77    inference(resolution,[],[f161,f98])).
% 2.94/0.77  fof(f98,plain,(
% 2.94/0.77    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f60])).
% 2.94/0.77  fof(f60,plain,(
% 2.94/0.77    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.94/0.77    inference(nnf_transformation,[],[f38])).
% 2.94/0.77  fof(f38,plain,(
% 2.94/0.77    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.94/0.77    inference(ennf_transformation,[],[f10])).
% 2.94/0.77  fof(f10,axiom,(
% 2.94/0.77    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.94/0.77  fof(f161,plain,(
% 2.94/0.77    v5_relat_1(sK3,sK0)),
% 2.94/0.77    inference(resolution,[],[f115,f76])).
% 2.94/0.77  fof(f115,plain,(
% 2.94/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f44])).
% 2.94/0.77  fof(f44,plain,(
% 2.94/0.77    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.77    inference(ennf_transformation,[],[f29])).
% 2.94/0.77  fof(f29,plain,(
% 2.94/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.94/0.77    inference(pure_predicate_removal,[],[f17])).
% 2.94/0.77  fof(f17,axiom,(
% 2.94/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.94/0.77  fof(f264,plain,(
% 2.94/0.77    v1_relat_1(sK3)),
% 2.94/0.77    inference(resolution,[],[f152,f76])).
% 2.94/0.77  fof(f152,plain,(
% 2.94/0.77    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_relat_1(X2)) )),
% 2.94/0.77    inference(resolution,[],[f88,f96])).
% 2.94/0.77  fof(f96,plain,(
% 2.94/0.77    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.94/0.77    inference(cnf_transformation,[],[f12])).
% 2.94/0.77  fof(f12,axiom,(
% 2.94/0.77    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.94/0.77  fof(f88,plain,(
% 2.94/0.77    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f33])).
% 2.94/0.77  fof(f33,plain,(
% 2.94/0.77    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.94/0.77    inference(ennf_transformation,[],[f9])).
% 2.94/0.77  fof(f9,axiom,(
% 2.94/0.77    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.94/0.77  fof(f1360,plain,(
% 2.94/0.77    ~r1_tarski(k2_relat_1(sK3),sK0) | sK0 = k2_relat_1(sK3)),
% 2.94/0.77    inference(forward_demodulation,[],[f1359,f86])).
% 2.94/0.77  fof(f86,plain,(
% 2.94/0.77    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.94/0.77    inference(cnf_transformation,[],[f14])).
% 2.94/0.77  fof(f14,axiom,(
% 2.94/0.77    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.94/0.77  fof(f1359,plain,(
% 2.94/0.77    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_relat_1(sK0))) | sK0 = k2_relat_1(sK3)),
% 2.94/0.77    inference(forward_demodulation,[],[f1358,f1291])).
% 2.94/0.77  fof(f1358,plain,(
% 2.94/0.77    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k5_relat_1(sK2,sK3)))),
% 2.94/0.77    inference(forward_demodulation,[],[f1330,f86])).
% 2.94/0.77  fof(f1330,plain,(
% 2.94/0.77    k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0)) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k5_relat_1(sK2,sK3)))),
% 2.94/0.77    inference(backward_demodulation,[],[f1250,f1291])).
% 2.94/0.77  fof(f1250,plain,(
% 2.94/0.77    k2_relat_1(sK3) = k2_relat_1(k5_relat_1(sK2,sK3)) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k5_relat_1(sK2,sK3)))),
% 2.94/0.77    inference(resolution,[],[f588,f107])).
% 2.94/0.77  fof(f107,plain,(
% 2.94/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f63])).
% 2.94/0.77  fof(f63,plain,(
% 2.94/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.94/0.77    inference(flattening,[],[f62])).
% 2.94/0.77  fof(f62,plain,(
% 2.94/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.94/0.77    inference(nnf_transformation,[],[f3])).
% 2.94/0.77  fof(f3,axiom,(
% 2.94/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.94/0.77  fof(f588,plain,(
% 2.94/0.77    r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))),
% 2.94/0.77    inference(resolution,[],[f316,f263])).
% 2.94/0.77  fof(f263,plain,(
% 2.94/0.77    v1_relat_1(sK2)),
% 2.94/0.77    inference(resolution,[],[f152,f73])).
% 2.94/0.77  fof(f316,plain,(
% 2.94/0.77    ( ! [X3] : (~v1_relat_1(X3) | r1_tarski(k2_relat_1(k5_relat_1(X3,sK3)),k2_relat_1(sK3))) )),
% 2.94/0.77    inference(resolution,[],[f264,f87])).
% 2.94/0.77  fof(f87,plain,(
% 2.94/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f32])).
% 2.94/0.77  fof(f32,plain,(
% 2.94/0.77    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.94/0.77    inference(ennf_transformation,[],[f13])).
% 2.94/0.77  fof(f13,axiom,(
% 2.94/0.77    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 2.94/0.77  fof(f617,plain,(
% 2.94/0.77    v2_funct_2(sK3,k2_relat_1(sK3))),
% 2.94/0.77    inference(subsumption_resolution,[],[f615,f264])).
% 2.94/0.77  fof(f615,plain,(
% 2.94/0.77    v2_funct_2(sK3,k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 2.94/0.77    inference(resolution,[],[f576,f123])).
% 2.94/0.77  fof(f123,plain,(
% 2.94/0.77    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.94/0.77    inference(equality_resolution,[],[f104])).
% 2.94/0.77  fof(f104,plain,(
% 2.94/0.77    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f61])).
% 2.94/0.77  fof(f61,plain,(
% 2.94/0.77    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.94/0.77    inference(nnf_transformation,[],[f43])).
% 2.94/0.77  fof(f43,plain,(
% 2.94/0.77    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.94/0.77    inference(flattening,[],[f42])).
% 2.94/0.77  fof(f42,plain,(
% 2.94/0.77    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.94/0.77    inference(ennf_transformation,[],[f22])).
% 2.94/0.77  fof(f22,axiom,(
% 2.94/0.77    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.94/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 2.94/0.77  fof(f576,plain,(
% 2.94/0.77    v5_relat_1(sK3,k2_relat_1(sK3))),
% 2.94/0.77    inference(resolution,[],[f317,f124])).
% 2.94/0.77  fof(f124,plain,(
% 2.94/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.94/0.77    inference(equality_resolution,[],[f106])).
% 2.94/0.77  fof(f106,plain,(
% 2.94/0.77    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.94/0.77    inference(cnf_transformation,[],[f63])).
% 2.94/0.77  fof(f317,plain,(
% 2.94/0.77    ( ! [X4] : (~r1_tarski(k2_relat_1(sK3),X4) | v5_relat_1(sK3,X4)) )),
% 2.94/0.77    inference(resolution,[],[f264,f99])).
% 2.94/0.77  fof(f99,plain,(
% 2.94/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f60])).
% 2.94/0.77  % SZS output end Proof for theBenchmark
% 2.94/0.77  % (21496)------------------------------
% 2.94/0.77  % (21496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.77  % (21496)Termination reason: Refutation
% 2.94/0.77  
% 2.94/0.77  % (21496)Memory used [KB]: 3198
% 2.94/0.77  % (21496)Time elapsed: 0.324 s
% 2.94/0.77  % (21496)------------------------------
% 2.94/0.77  % (21496)------------------------------
% 2.94/0.78  % (21488)Success in time 0.407 s
%------------------------------------------------------------------------------
