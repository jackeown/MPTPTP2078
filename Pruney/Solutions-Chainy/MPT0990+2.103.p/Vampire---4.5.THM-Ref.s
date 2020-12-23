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
% DateTime   : Thu Dec  3 13:02:46 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  199 (1668 expanded)
%              Number of leaves         :   25 ( 523 expanded)
%              Depth                    :   28
%              Number of atoms          :  796 (16641 expanded)
%              Number of equality atoms :  232 (5666 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1252,f720])).

fof(f720,plain,(
    sK3 != k4_relat_1(sK2) ),
    inference(superposition,[],[f100,f422])).

fof(f422,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f415,f222])).

fof(f222,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f220,f89])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f81,f80])).

fof(f80,plain,
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

fof(f81,plain,
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

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f39])).

fof(f39,negated_conjecture,(
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
    inference(negated_conjecture,[],[f38])).

fof(f38,conjecture,(
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

fof(f220,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f118,f97])).

fof(f97,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f415,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f189,f91])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

fof(f189,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f117,f125])).

fof(f125,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f100,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f82])).

fof(f1252,plain,(
    sK3 = k4_relat_1(sK2) ),
    inference(backward_demodulation,[],[f499,f1250])).

fof(f1250,plain,(
    sK2 = k4_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1249,f415])).

fof(f1249,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1248,f424])).

fof(f424,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f415,f282])).

fof(f282,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f280,f107])).

fof(f107,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f280,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f253,f279])).

fof(f279,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f278,f89])).

fof(f278,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f277,f91])).

fof(f277,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f276,f95])).

fof(f95,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f276,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f275,f97])).

fof(f275,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f273,f99])).

fof(f99,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f82])).

fof(f273,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f165,f90])).

fof(f90,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f143,f101])).

fof(f101,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f253,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f251,f89])).

fof(f251,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f122,f97])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f1248,plain,
    ( sK2 = k4_relat_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1242,f991])).

fof(f991,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f849,f826])).

fof(f826,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f824,f821])).

fof(f821,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f635,f94])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f82])).

fof(f635,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) ) ),
    inference(resolution,[],[f346,f91])).

fof(f346,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(X0,X1,X2,X3,sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f270,f89])).

fof(f270,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f153,f92])).

fof(f92,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f153,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f824,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f260,f821])).

fof(f260,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f259,f164])).

fof(f164,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f105,f101])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f259,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f151,f163])).

fof(f163,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f96,f101])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f849,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f848,f821])).

fof(f848,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f639,f94])).

fof(f639,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f350,f91])).

fof(f350,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f272,f89])).

fof(f272,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f155,f92])).

fof(f155,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1242,plain,
    ( sK2 = k4_relat_1(sK3)
    | k6_relat_1(sK0) != k5_relat_1(sK2,sK3)
    | sK1 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1183,f89])).

fof(f1183,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k4_relat_1(sK3) = X0
      | k6_relat_1(sK0) != k5_relat_1(X0,sK3)
      | k2_relat_1(X0) != sK1
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f1090,f1142])).

fof(f1142,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f1022,f669])).

fof(f669,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK3))
    | sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f497,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f497,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(resolution,[],[f416,f256])).

fof(f256,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(resolution,[],[f212,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f212,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f140,f94])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f416,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f189,f94])).

fof(f1022,plain,(
    r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f998,f106])).

fof(f106,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f998,plain,
    ( sK0 != k1_relat_1(k6_relat_1(sK0))
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f464,f991])).

fof(f464,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f454,f424])).

fof(f454,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f453,f416])).

fof(f453,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f445,f415])).

fof(f445,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f331,f423])).

fof(f423,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f415,f296])).

fof(f296,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f294,f107])).

fof(f294,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f243,f293])).

fof(f293,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f292,f89])).

fof(f292,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f291,f91])).

fof(f291,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f290,f95])).

fof(f290,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f289,f97])).

fof(f289,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f287,f99])).

fof(f287,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f166,f90])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f142,f101])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f243,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f241,f89])).

fof(f241,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f120,f97])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f331,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f257,f92])).

fof(f257,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r1_tarski(k2_relat_1(sK2),k1_relat_1(X0))
      | ~ v1_relat_1(sK2)
      | k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f123,f89])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f1090,plain,(
    ! [X0] :
      ( k4_relat_1(sK3) = X0
      | k6_relat_1(sK0) != k5_relat_1(X0,sK3)
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f1073,f1085])).

fof(f1085,plain,(
    k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1084,f416])).

fof(f1084,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1070,f92])).

fof(f1070,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f1024,f118])).

fof(f1024,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1003,f104])).

fof(f104,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1003,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f823,f991])).

fof(f823,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f370,f821])).

fof(f370,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f369,f89])).

fof(f369,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f368,f95])).

fof(f368,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f367,f91])).

fof(f367,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f325,f90])).

fof(f325,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,X2,sK1)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f324,f92])).

fof(f324,plain,(
    ! [X2,X3] :
      ( sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f323,f94])).

fof(f323,plain,(
    ! [X2,X3] :
      ( sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f322,f98])).

fof(f98,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f82])).

fof(f322,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f149,f93])).

fof(f93,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f149,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f1073,plain,(
    ! [X0] :
      ( k6_relat_1(sK0) != k5_relat_1(X0,sK3)
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | k2_funct_1(sK3) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f1072,f496])).

fof(f496,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f416,f372])).

fof(f372,plain,
    ( ~ v1_relat_1(sK3)
    | sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f371,f215])).

fof(f215,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f141,f94])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f371,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f362,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f362,plain,(
    v2_funct_2(sK3,sK0) ),
    inference(subsumption_resolution,[],[f361,f89])).

fof(f361,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f360,f91])).

fof(f360,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v2_funct_2(sK3,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f359,f163])).

fof(f359,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v2_funct_2(sK3,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f312,f90])).

fof(f312,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,sK0,sK1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_relat_1(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v2_funct_2(sK3,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f311,f92])).

fof(f311,plain,(
    ! [X1] :
      ( v2_funct_2(sK3,sK0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_relat_1(sK0))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X1,sK0,sK1)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f308,f94])).

fof(f308,plain,(
    ! [X1] :
      ( v2_funct_2(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_relat_1(sK0))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X1,sK0,sK1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f167,f93])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | v2_funct_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f145,f101])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
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

fof(f1072,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK3) != k6_relat_1(k2_relat_1(sK3))
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | k2_funct_1(sK3) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1071,f416])).

fof(f1071,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK3) != k6_relat_1(k2_relat_1(sK3))
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | k2_funct_1(sK3) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f1065,f92])).

fof(f1065,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK3) != k6_relat_1(k2_relat_1(sK3))
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | k2_funct_1(sK3) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f1024,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f499,plain,(
    sK3 = k4_relat_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f416,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:54:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (15808)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15824)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (15807)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (15816)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (15803)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (15806)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (15804)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (15811)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (15831)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (15810)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (15825)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (15822)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (15817)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.47/0.55  % (15829)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.55  % (15805)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.47/0.55  % (15802)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.47/0.55  % (15823)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.47/0.55  % (15809)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.47/0.56  % (15827)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.47/0.56  % (15821)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.47/0.56  % (15826)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.56  % (15820)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.47/0.56  % (15819)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.56  % (15815)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.47/0.56  % (15813)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.47/0.56  % (15818)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.47/0.56  % (15814)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.47/0.56  % (15830)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.47/0.57  % (15818)Refutation not found, incomplete strategy% (15818)------------------------------
% 1.47/0.57  % (15818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (15812)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.57/0.58  % (15818)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (15818)Memory used [KB]: 10746
% 1.57/0.58  % (15818)Time elapsed: 0.159 s
% 1.57/0.58  % (15818)------------------------------
% 1.57/0.58  % (15818)------------------------------
% 1.57/0.58  % (15828)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.03/0.65  % (15809)Refutation found. Thanks to Tanya!
% 2.03/0.65  % SZS status Theorem for theBenchmark
% 2.03/0.65  % SZS output start Proof for theBenchmark
% 2.03/0.65  fof(f1301,plain,(
% 2.03/0.65    $false),
% 2.03/0.65    inference(subsumption_resolution,[],[f1252,f720])).
% 2.03/0.65  fof(f720,plain,(
% 2.03/0.65    sK3 != k4_relat_1(sK2)),
% 2.03/0.65    inference(superposition,[],[f100,f422])).
% 2.03/0.65  fof(f422,plain,(
% 2.03/0.65    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.03/0.65    inference(resolution,[],[f415,f222])).
% 2.03/0.65  fof(f222,plain,(
% 2.03/0.65    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.03/0.65    inference(subsumption_resolution,[],[f220,f89])).
% 2.03/0.65  fof(f89,plain,(
% 2.03/0.65    v1_funct_1(sK2)),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f82,plain,(
% 2.03/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.03/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f81,f80])).
% 2.03/0.65  fof(f80,plain,(
% 2.03/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.03/0.65    introduced(choice_axiom,[])).
% 2.03/0.65  fof(f81,plain,(
% 2.03/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.03/0.65    introduced(choice_axiom,[])).
% 2.03/0.65  fof(f43,plain,(
% 2.03/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.03/0.65    inference(flattening,[],[f42])).
% 2.03/0.65  fof(f42,plain,(
% 2.03/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.03/0.65    inference(ennf_transformation,[],[f39])).
% 2.03/0.65  fof(f39,negated_conjecture,(
% 2.03/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.03/0.65    inference(negated_conjecture,[],[f38])).
% 2.03/0.65  fof(f38,conjecture,(
% 2.03/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.03/0.65  fof(f220,plain,(
% 2.03/0.65    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.03/0.65    inference(resolution,[],[f118,f97])).
% 2.03/0.65  fof(f97,plain,(
% 2.03/0.65    v2_funct_1(sK2)),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f118,plain,(
% 2.03/0.65    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f54])).
% 2.03/0.65  fof(f54,plain,(
% 2.03/0.65    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.03/0.65    inference(flattening,[],[f53])).
% 2.03/0.65  fof(f53,plain,(
% 2.03/0.65    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.03/0.65    inference(ennf_transformation,[],[f22])).
% 2.03/0.65  fof(f22,axiom,(
% 2.03/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 2.03/0.65  fof(f415,plain,(
% 2.03/0.65    v1_relat_1(sK2)),
% 2.03/0.65    inference(resolution,[],[f189,f91])).
% 2.03/0.65  fof(f91,plain,(
% 2.03/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f189,plain,(
% 2.03/0.65    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_relat_1(X2)) )),
% 2.03/0.65    inference(resolution,[],[f117,f125])).
% 2.03/0.65  fof(f125,plain,(
% 2.03/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.03/0.65    inference(cnf_transformation,[],[f11])).
% 2.03/0.65  fof(f11,axiom,(
% 2.03/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.03/0.65  fof(f117,plain,(
% 2.03/0.65    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f52])).
% 2.03/0.65  fof(f52,plain,(
% 2.03/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.03/0.65    inference(ennf_transformation,[],[f8])).
% 2.03/0.65  fof(f8,axiom,(
% 2.03/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.03/0.65  fof(f100,plain,(
% 2.03/0.65    k2_funct_1(sK2) != sK3),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f1252,plain,(
% 2.03/0.65    sK3 = k4_relat_1(sK2)),
% 2.03/0.65    inference(backward_demodulation,[],[f499,f1250])).
% 2.03/0.65  fof(f1250,plain,(
% 2.03/0.65    sK2 = k4_relat_1(sK3)),
% 2.03/0.65    inference(subsumption_resolution,[],[f1249,f415])).
% 2.03/0.65  fof(f1249,plain,(
% 2.03/0.65    sK2 = k4_relat_1(sK3) | ~v1_relat_1(sK2)),
% 2.03/0.65    inference(subsumption_resolution,[],[f1248,f424])).
% 2.03/0.65  fof(f424,plain,(
% 2.03/0.65    sK1 = k2_relat_1(sK2)),
% 2.03/0.65    inference(resolution,[],[f415,f282])).
% 2.03/0.65  fof(f282,plain,(
% 2.03/0.65    ~v1_relat_1(sK2) | sK1 = k2_relat_1(sK2)),
% 2.03/0.65    inference(forward_demodulation,[],[f280,f107])).
% 2.03/0.65  fof(f107,plain,(
% 2.03/0.65    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.03/0.65    inference(cnf_transformation,[],[f18])).
% 2.03/0.65  fof(f18,axiom,(
% 2.03/0.65    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.03/0.65  fof(f280,plain,(
% 2.03/0.65    k2_relat_1(sK2) = k2_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2)),
% 2.03/0.65    inference(backward_demodulation,[],[f253,f279])).
% 2.03/0.65  fof(f279,plain,(
% 2.03/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 2.03/0.65    inference(subsumption_resolution,[],[f278,f89])).
% 2.03/0.65  fof(f278,plain,(
% 2.03/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2)),
% 2.03/0.65    inference(subsumption_resolution,[],[f277,f91])).
% 2.03/0.65  fof(f277,plain,(
% 2.03/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2)),
% 2.03/0.65    inference(subsumption_resolution,[],[f276,f95])).
% 2.03/0.65  fof(f95,plain,(
% 2.03/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f276,plain,(
% 2.03/0.65    sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2)),
% 2.03/0.65    inference(subsumption_resolution,[],[f275,f97])).
% 2.03/0.65  fof(f275,plain,(
% 2.03/0.65    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2)),
% 2.03/0.65    inference(subsumption_resolution,[],[f273,f99])).
% 2.03/0.65  fof(f99,plain,(
% 2.03/0.65    k1_xboole_0 != sK1),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f273,plain,(
% 2.03/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2)),
% 2.03/0.65    inference(resolution,[],[f165,f90])).
% 2.03/0.65  fof(f90,plain,(
% 2.03/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f165,plain,(
% 2.03/0.65    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~v1_funct_1(X2)) )),
% 2.03/0.65    inference(forward_demodulation,[],[f143,f101])).
% 2.03/0.65  fof(f101,plain,(
% 2.03/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f34])).
% 2.03/0.65  fof(f34,axiom,(
% 2.03/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.03/0.65  fof(f143,plain,(
% 2.03/0.65    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f69])).
% 2.03/0.65  fof(f69,plain,(
% 2.03/0.65    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.03/0.65    inference(flattening,[],[f68])).
% 2.03/0.65  fof(f68,plain,(
% 2.03/0.65    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.03/0.65    inference(ennf_transformation,[],[f37])).
% 2.03/0.65  fof(f37,axiom,(
% 2.03/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.03/0.65  fof(f253,plain,(
% 2.03/0.65    k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2)),
% 2.03/0.65    inference(subsumption_resolution,[],[f251,f89])).
% 2.03/0.65  fof(f251,plain,(
% 2.03/0.65    k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.03/0.65    inference(resolution,[],[f122,f97])).
% 2.03/0.65  fof(f122,plain,(
% 2.03/0.65    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f58])).
% 2.03/0.65  fof(f58,plain,(
% 2.03/0.65    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.03/0.65    inference(flattening,[],[f57])).
% 2.03/0.65  fof(f57,plain,(
% 2.03/0.65    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.03/0.65    inference(ennf_transformation,[],[f26])).
% 2.03/0.65  fof(f26,axiom,(
% 2.03/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 2.03/0.65  fof(f1248,plain,(
% 2.03/0.65    sK2 = k4_relat_1(sK3) | sK1 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.03/0.65    inference(subsumption_resolution,[],[f1242,f991])).
% 2.03/0.65  fof(f991,plain,(
% 2.03/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.03/0.65    inference(resolution,[],[f849,f826])).
% 2.03/0.65  fof(f826,plain,(
% 2.03/0.65    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.03/0.65    inference(forward_demodulation,[],[f824,f821])).
% 2.03/0.65  fof(f821,plain,(
% 2.03/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.03/0.65    inference(resolution,[],[f635,f94])).
% 2.03/0.65  fof(f94,plain,(
% 2.03/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f635,plain,(
% 2.03/0.65    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3)) )),
% 2.03/0.65    inference(resolution,[],[f346,f91])).
% 2.03/0.65  fof(f346,plain,(
% 2.03/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK3) = k1_partfun1(X0,X1,X2,X3,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.03/0.65    inference(resolution,[],[f270,f89])).
% 2.03/0.65  fof(f270,plain,(
% 2.03/0.65    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 2.03/0.65    inference(resolution,[],[f153,f92])).
% 2.03/0.65  fof(f92,plain,(
% 2.03/0.65    v1_funct_1(sK3)),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f153,plain,(
% 2.03/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f77])).
% 2.03/0.65  fof(f77,plain,(
% 2.03/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.03/0.65    inference(flattening,[],[f76])).
% 2.03/0.65  fof(f76,plain,(
% 2.03/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.03/0.65    inference(ennf_transformation,[],[f33])).
% 2.03/0.65  fof(f33,axiom,(
% 2.03/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.03/0.65  fof(f824,plain,(
% 2.03/0.65    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.03/0.65    inference(backward_demodulation,[],[f260,f821])).
% 2.03/0.65  fof(f260,plain,(
% 2.03/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.03/0.65    inference(subsumption_resolution,[],[f259,f164])).
% 2.03/0.65  fof(f164,plain,(
% 2.03/0.65    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f105,f101])).
% 2.03/0.65  fof(f105,plain,(
% 2.03/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.03/0.65    inference(cnf_transformation,[],[f41])).
% 2.03/0.65  fof(f41,plain,(
% 2.03/0.65    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.03/0.65    inference(pure_predicate_removal,[],[f32])).
% 2.03/0.65  fof(f32,axiom,(
% 2.03/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.03/0.65  fof(f259,plain,(
% 2.03/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.03/0.65    inference(resolution,[],[f151,f163])).
% 2.03/0.65  fof(f163,plain,(
% 2.03/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.03/0.65    inference(forward_demodulation,[],[f96,f101])).
% 2.03/0.65  fof(f96,plain,(
% 2.03/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.03/0.65    inference(cnf_transformation,[],[f82])).
% 2.03/0.65  fof(f151,plain,(
% 2.03/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/0.65    inference(cnf_transformation,[],[f88])).
% 2.03/0.65  fof(f88,plain,(
% 2.03/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.65    inference(nnf_transformation,[],[f75])).
% 2.03/0.65  fof(f75,plain,(
% 2.03/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.65    inference(flattening,[],[f74])).
% 2.03/0.65  fof(f74,plain,(
% 2.03/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.03/0.65    inference(ennf_transformation,[],[f29])).
% 2.03/0.65  fof(f29,axiom,(
% 2.03/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.03/0.65  fof(f849,plain,(
% 2.03/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.03/0.65    inference(forward_demodulation,[],[f848,f821])).
% 2.03/0.65  fof(f848,plain,(
% 2.03/0.65    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.03/0.65    inference(resolution,[],[f639,f94])).
% 2.03/0.65  fof(f639,plain,(
% 2.03/0.65    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 2.03/0.65    inference(resolution,[],[f350,f91])).
% 2.03/0.65  fof(f350,plain,(
% 2.03/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.03/0.65    inference(resolution,[],[f272,f89])).
% 2.03/0.65  fof(f272,plain,(
% 2.03/0.65    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 2.03/0.65    inference(resolution,[],[f155,f92])).
% 2.03/0.65  fof(f155,plain,(
% 2.03/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f79])).
% 2.03/0.65  fof(f79,plain,(
% 2.03/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.03/0.65    inference(flattening,[],[f78])).
% 2.03/0.65  fof(f78,plain,(
% 2.03/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.03/0.65    inference(ennf_transformation,[],[f31])).
% 2.03/0.65  fof(f31,axiom,(
% 2.03/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.03/0.66  fof(f1242,plain,(
% 2.03/0.66    sK2 = k4_relat_1(sK3) | k6_relat_1(sK0) != k5_relat_1(sK2,sK3) | sK1 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.03/0.66    inference(resolution,[],[f1183,f89])).
% 2.03/0.66  fof(f1183,plain,(
% 2.03/0.66    ( ! [X0] : (~v1_funct_1(X0) | k4_relat_1(sK3) = X0 | k6_relat_1(sK0) != k5_relat_1(X0,sK3) | k2_relat_1(X0) != sK1 | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(backward_demodulation,[],[f1090,f1142])).
% 2.03/0.66  fof(f1142,plain,(
% 2.03/0.66    sK1 = k1_relat_1(sK3)),
% 2.03/0.66    inference(resolution,[],[f1022,f669])).
% 2.03/0.66  fof(f669,plain,(
% 2.03/0.66    ~r1_tarski(sK1,k1_relat_1(sK3)) | sK1 = k1_relat_1(sK3)),
% 2.03/0.66    inference(resolution,[],[f497,f136])).
% 2.03/0.66  fof(f136,plain,(
% 2.03/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f86])).
% 2.03/0.66  fof(f86,plain,(
% 2.03/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.66    inference(flattening,[],[f85])).
% 2.03/0.66  fof(f85,plain,(
% 2.03/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.66    inference(nnf_transformation,[],[f2])).
% 2.03/0.66  fof(f2,axiom,(
% 2.03/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.03/0.66  fof(f497,plain,(
% 2.03/0.66    r1_tarski(k1_relat_1(sK3),sK1)),
% 2.03/0.66    inference(resolution,[],[f416,f256])).
% 2.03/0.66  fof(f256,plain,(
% 2.03/0.66    ~v1_relat_1(sK3) | r1_tarski(k1_relat_1(sK3),sK1)),
% 2.03/0.66    inference(resolution,[],[f212,f130])).
% 2.03/0.66  fof(f130,plain,(
% 2.03/0.66    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f83])).
% 2.03/0.66  fof(f83,plain,(
% 2.03/0.66    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.03/0.66    inference(nnf_transformation,[],[f64])).
% 2.03/0.66  fof(f64,plain,(
% 2.03/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.03/0.66    inference(ennf_transformation,[],[f9])).
% 2.03/0.66  fof(f9,axiom,(
% 2.03/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.03/0.66  fof(f212,plain,(
% 2.03/0.66    v4_relat_1(sK3,sK1)),
% 2.03/0.66    inference(resolution,[],[f140,f94])).
% 2.03/0.66  fof(f140,plain,(
% 2.03/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f67])).
% 2.03/0.66  fof(f67,plain,(
% 2.03/0.66    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.66    inference(ennf_transformation,[],[f28])).
% 2.03/0.66  fof(f28,axiom,(
% 2.03/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.03/0.66  fof(f416,plain,(
% 2.03/0.66    v1_relat_1(sK3)),
% 2.03/0.66    inference(resolution,[],[f189,f94])).
% 2.03/0.66  fof(f1022,plain,(
% 2.03/0.66    r1_tarski(sK1,k1_relat_1(sK3))),
% 2.03/0.66    inference(subsumption_resolution,[],[f998,f106])).
% 2.03/0.66  fof(f106,plain,(
% 2.03/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.03/0.66    inference(cnf_transformation,[],[f18])).
% 2.03/0.66  fof(f998,plain,(
% 2.03/0.66    sK0 != k1_relat_1(k6_relat_1(sK0)) | r1_tarski(sK1,k1_relat_1(sK3))),
% 2.03/0.66    inference(backward_demodulation,[],[f464,f991])).
% 2.03/0.66  fof(f464,plain,(
% 2.03/0.66    sK0 != k1_relat_1(k5_relat_1(sK2,sK3)) | r1_tarski(sK1,k1_relat_1(sK3))),
% 2.03/0.66    inference(backward_demodulation,[],[f454,f424])).
% 2.03/0.66  fof(f454,plain,(
% 2.03/0.66    sK0 != k1_relat_1(k5_relat_1(sK2,sK3)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))),
% 2.03/0.66    inference(subsumption_resolution,[],[f453,f416])).
% 2.03/0.66  fof(f453,plain,(
% 2.03/0.66    sK0 != k1_relat_1(k5_relat_1(sK2,sK3)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 2.03/0.66    inference(subsumption_resolution,[],[f445,f415])).
% 2.03/0.66  fof(f445,plain,(
% 2.03/0.66    sK0 != k1_relat_1(k5_relat_1(sK2,sK3)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3)),
% 2.03/0.66    inference(backward_demodulation,[],[f331,f423])).
% 2.03/0.66  fof(f423,plain,(
% 2.03/0.66    sK0 = k1_relat_1(sK2)),
% 2.03/0.66    inference(resolution,[],[f415,f296])).
% 2.03/0.66  fof(f296,plain,(
% 2.03/0.66    ~v1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 2.03/0.66    inference(forward_demodulation,[],[f294,f107])).
% 2.03/0.66  fof(f294,plain,(
% 2.03/0.66    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2)),
% 2.03/0.66    inference(backward_demodulation,[],[f243,f293])).
% 2.03/0.66  fof(f293,plain,(
% 2.03/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.03/0.66    inference(subsumption_resolution,[],[f292,f89])).
% 2.03/0.66  fof(f292,plain,(
% 2.03/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.03/0.66    inference(subsumption_resolution,[],[f291,f91])).
% 2.03/0.66  fof(f291,plain,(
% 2.03/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.03/0.66    inference(subsumption_resolution,[],[f290,f95])).
% 2.03/0.66  fof(f290,plain,(
% 2.03/0.66    sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.03/0.66    inference(subsumption_resolution,[],[f289,f97])).
% 2.03/0.66  fof(f289,plain,(
% 2.03/0.66    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.03/0.66    inference(subsumption_resolution,[],[f287,f99])).
% 2.03/0.66  fof(f287,plain,(
% 2.03/0.66    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.03/0.66    inference(resolution,[],[f166,f90])).
% 2.03/0.66  fof(f166,plain,(
% 2.03/0.66    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v1_funct_1(X2)) )),
% 2.03/0.66    inference(forward_demodulation,[],[f142,f101])).
% 2.03/0.66  fof(f142,plain,(
% 2.03/0.66    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f69])).
% 2.03/0.66  fof(f243,plain,(
% 2.03/0.66    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 2.03/0.66    inference(subsumption_resolution,[],[f241,f89])).
% 2.03/0.66  fof(f241,plain,(
% 2.03/0.66    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.03/0.66    inference(resolution,[],[f120,f97])).
% 2.03/0.66  fof(f120,plain,(
% 2.03/0.66    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f56])).
% 2.03/0.66  fof(f56,plain,(
% 2.03/0.66    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.03/0.66    inference(flattening,[],[f55])).
% 2.03/0.66  fof(f55,plain,(
% 2.03/0.66    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.03/0.66    inference(ennf_transformation,[],[f25])).
% 2.03/0.66  fof(f25,axiom,(
% 2.03/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 2.03/0.66  fof(f331,plain,(
% 2.03/0.66    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3)),
% 2.03/0.66    inference(resolution,[],[f257,f92])).
% 2.03/0.66  fof(f257,plain,(
% 2.03/0.66    ( ! [X0] : (~v1_funct_1(X0) | r1_tarski(k2_relat_1(sK2),k1_relat_1(X0)) | ~v1_relat_1(sK2) | k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(resolution,[],[f123,f89])).
% 2.03/0.66  fof(f123,plain,(
% 2.03/0.66    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f60])).
% 2.03/0.66  fof(f60,plain,(
% 2.03/0.66    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.03/0.66    inference(flattening,[],[f59])).
% 2.03/0.66  fof(f59,plain,(
% 2.03/0.66    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.03/0.66    inference(ennf_transformation,[],[f24])).
% 2.03/0.66  fof(f24,axiom,(
% 2.03/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 2.03/0.66  fof(f1090,plain,(
% 2.03/0.66    ( ! [X0] : (k4_relat_1(sK3) = X0 | k6_relat_1(sK0) != k5_relat_1(X0,sK3) | k2_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(backward_demodulation,[],[f1073,f1085])).
% 2.03/0.66  fof(f1085,plain,(
% 2.03/0.66    k2_funct_1(sK3) = k4_relat_1(sK3)),
% 2.03/0.66    inference(subsumption_resolution,[],[f1084,f416])).
% 2.03/0.66  fof(f1084,plain,(
% 2.03/0.66    k2_funct_1(sK3) = k4_relat_1(sK3) | ~v1_relat_1(sK3)),
% 2.03/0.66    inference(subsumption_resolution,[],[f1070,f92])).
% 2.03/0.66  fof(f1070,plain,(
% 2.03/0.66    k2_funct_1(sK3) = k4_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.03/0.66    inference(resolution,[],[f1024,f118])).
% 2.24/0.66  fof(f1024,plain,(
% 2.24/0.66    v2_funct_1(sK3)),
% 2.24/0.66    inference(subsumption_resolution,[],[f1003,f104])).
% 2.24/0.66  fof(f104,plain,(
% 2.24/0.66    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.24/0.66    inference(cnf_transformation,[],[f23])).
% 2.24/0.66  fof(f23,axiom,(
% 2.24/0.66    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.24/0.66  fof(f1003,plain,(
% 2.24/0.66    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3)),
% 2.24/0.66    inference(backward_demodulation,[],[f823,f991])).
% 2.24/0.66  fof(f823,plain,(
% 2.24/0.66    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3)),
% 2.24/0.66    inference(backward_demodulation,[],[f370,f821])).
% 2.24/0.66  fof(f370,plain,(
% 2.24/0.66    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 2.24/0.66    inference(subsumption_resolution,[],[f369,f89])).
% 2.24/0.66  fof(f369,plain,(
% 2.24/0.66    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | ~v1_funct_1(sK2)),
% 2.24/0.66    inference(subsumption_resolution,[],[f368,f95])).
% 2.24/0.66  fof(f368,plain,(
% 2.24/0.66    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v1_funct_1(sK2)),
% 2.24/0.66    inference(subsumption_resolution,[],[f367,f91])).
% 2.24/0.66  fof(f367,plain,(
% 2.24/0.66    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v1_funct_1(sK2)),
% 2.24/0.66    inference(resolution,[],[f325,f90])).
% 2.24/0.66  fof(f325,plain,(
% 2.24/0.66    ( ! [X2,X3] : (~v1_funct_2(X3,X2,sK1) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | sK1 != k2_relset_1(X2,sK1,X3) | ~v1_funct_1(X3)) )),
% 2.24/0.66    inference(subsumption_resolution,[],[f324,f92])).
% 2.24/0.66  fof(f324,plain,(
% 2.24/0.66    ( ! [X2,X3] : (sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 2.24/0.66    inference(subsumption_resolution,[],[f323,f94])).
% 2.24/0.66  fof(f323,plain,(
% 2.24/0.66    ( ! [X2,X3] : (sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 2.24/0.66    inference(subsumption_resolution,[],[f322,f98])).
% 2.24/0.66  fof(f98,plain,(
% 2.24/0.66    k1_xboole_0 != sK0),
% 2.24/0.66    inference(cnf_transformation,[],[f82])).
% 2.24/0.66  fof(f322,plain,(
% 2.24/0.66    ( ! [X2,X3] : (k1_xboole_0 = sK0 | sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 2.24/0.66    inference(resolution,[],[f149,f93])).
% 2.24/0.66  fof(f93,plain,(
% 2.24/0.66    v1_funct_2(sK3,sK1,sK0)),
% 2.24/0.66    inference(cnf_transformation,[],[f82])).
% 2.24/0.66  fof(f149,plain,(
% 2.24/0.66    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,X1,X2) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_1(X4) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f73])).
% 2.24/0.66  fof(f73,plain,(
% 2.24/0.66    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.24/0.66    inference(flattening,[],[f72])).
% 2.24/0.66  fof(f72,plain,(
% 2.24/0.66    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.24/0.66    inference(ennf_transformation,[],[f36])).
% 2.24/0.66  fof(f36,axiom,(
% 2.24/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.24/0.66  fof(f1073,plain,(
% 2.24/0.66    ( ! [X0] : (k6_relat_1(sK0) != k5_relat_1(X0,sK3) | k2_relat_1(X0) != k1_relat_1(sK3) | k2_funct_1(sK3) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.66    inference(forward_demodulation,[],[f1072,f496])).
% 2.24/0.66  fof(f496,plain,(
% 2.24/0.66    sK0 = k2_relat_1(sK3)),
% 2.24/0.66    inference(resolution,[],[f416,f372])).
% 2.24/0.66  fof(f372,plain,(
% 2.24/0.66    ~v1_relat_1(sK3) | sK0 = k2_relat_1(sK3)),
% 2.24/0.66    inference(subsumption_resolution,[],[f371,f215])).
% 2.24/0.66  fof(f215,plain,(
% 2.24/0.66    v5_relat_1(sK3,sK0)),
% 2.24/0.66    inference(resolution,[],[f141,f94])).
% 2.24/0.66  fof(f141,plain,(
% 2.24/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f67])).
% 2.24/0.66  fof(f371,plain,(
% 2.24/0.66    sK0 = k2_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3)),
% 2.24/0.66    inference(resolution,[],[f362,f132])).
% 2.24/0.66  fof(f132,plain,(
% 2.24/0.66    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f84])).
% 2.24/0.66  fof(f84,plain,(
% 2.24/0.66    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.24/0.66    inference(nnf_transformation,[],[f66])).
% 2.24/0.66  fof(f66,plain,(
% 2.24/0.66    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.24/0.66    inference(flattening,[],[f65])).
% 2.24/0.66  fof(f65,plain,(
% 2.24/0.66    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.24/0.66    inference(ennf_transformation,[],[f30])).
% 2.24/0.66  fof(f30,axiom,(
% 2.24/0.66    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 2.24/0.66  fof(f362,plain,(
% 2.24/0.66    v2_funct_2(sK3,sK0)),
% 2.24/0.66    inference(subsumption_resolution,[],[f361,f89])).
% 2.24/0.66  fof(f361,plain,(
% 2.24/0.66    v2_funct_2(sK3,sK0) | ~v1_funct_1(sK2)),
% 2.24/0.66    inference(subsumption_resolution,[],[f360,f91])).
% 2.24/0.66  fof(f360,plain,(
% 2.24/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v2_funct_2(sK3,sK0) | ~v1_funct_1(sK2)),
% 2.24/0.66    inference(subsumption_resolution,[],[f359,f163])).
% 2.24/0.66  fof(f359,plain,(
% 2.24/0.66    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v2_funct_2(sK3,sK0) | ~v1_funct_1(sK2)),
% 2.24/0.66    inference(resolution,[],[f312,f90])).
% 2.24/0.66  fof(f312,plain,(
% 2.24/0.66    ( ! [X1] : (~v1_funct_2(X1,sK0,sK1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_relat_1(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v2_funct_2(sK3,sK0) | ~v1_funct_1(X1)) )),
% 2.24/0.66    inference(subsumption_resolution,[],[f311,f92])).
% 2.24/0.66  fof(f311,plain,(
% 2.24/0.66    ( ! [X1] : (v2_funct_2(sK3,sK0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(X1,sK0,sK1) | ~v1_funct_1(X1)) )),
% 2.24/0.66    inference(subsumption_resolution,[],[f308,f94])).
% 2.24/0.66  fof(f308,plain,(
% 2.24/0.66    ( ! [X1] : (v2_funct_2(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(X1,sK0,sK1) | ~v1_funct_1(X1)) )),
% 2.24/0.66    inference(resolution,[],[f167,f93])).
% 2.24/0.66  fof(f167,plain,(
% 2.24/0.66    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | v2_funct_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.24/0.66    inference(forward_demodulation,[],[f145,f101])).
% 2.24/0.66  fof(f145,plain,(
% 2.24/0.66    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f71])).
% 2.24/0.66  fof(f71,plain,(
% 2.24/0.66    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.24/0.66    inference(flattening,[],[f70])).
% 2.24/0.66  fof(f70,plain,(
% 2.24/0.66    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.24/0.66    inference(ennf_transformation,[],[f35])).
% 2.24/0.66  fof(f35,axiom,(
% 2.24/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 2.24/0.66  fof(f1072,plain,(
% 2.24/0.66    ( ! [X0] : (k5_relat_1(X0,sK3) != k6_relat_1(k2_relat_1(sK3)) | k2_relat_1(X0) != k1_relat_1(sK3) | k2_funct_1(sK3) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.66    inference(subsumption_resolution,[],[f1071,f416])).
% 2.24/0.66  fof(f1071,plain,(
% 2.24/0.66    ( ! [X0] : (k5_relat_1(X0,sK3) != k6_relat_1(k2_relat_1(sK3)) | k2_relat_1(X0) != k1_relat_1(sK3) | k2_funct_1(sK3) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) )),
% 2.24/0.66    inference(subsumption_resolution,[],[f1065,f92])).
% 2.24/0.66  fof(f1065,plain,(
% 2.24/0.66    ( ! [X0] : (k5_relat_1(X0,sK3) != k6_relat_1(k2_relat_1(sK3)) | k2_relat_1(X0) != k1_relat_1(sK3) | k2_funct_1(sK3) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 2.24/0.66    inference(resolution,[],[f1024,f124])).
% 2.24/0.66  fof(f124,plain,(
% 2.24/0.66    ( ! [X0,X1] : (~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f62])).
% 2.24/0.66  fof(f62,plain,(
% 2.24/0.66    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.24/0.66    inference(flattening,[],[f61])).
% 2.24/0.66  fof(f61,plain,(
% 2.24/0.66    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.24/0.66    inference(ennf_transformation,[],[f27])).
% 2.24/0.66  fof(f27,axiom,(
% 2.24/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 2.24/0.66  fof(f499,plain,(
% 2.24/0.66    sK3 = k4_relat_1(k4_relat_1(sK3))),
% 2.24/0.66    inference(resolution,[],[f416,f109])).
% 2.24/0.66  fof(f109,plain,(
% 2.24/0.66    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 2.24/0.66    inference(cnf_transformation,[],[f45])).
% 2.24/0.66  fof(f45,plain,(
% 2.24/0.66    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.24/0.66    inference(ennf_transformation,[],[f12])).
% 2.24/0.66  fof(f12,axiom,(
% 2.24/0.66    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 2.24/0.66  % SZS output end Proof for theBenchmark
% 2.24/0.66  % (15809)------------------------------
% 2.24/0.66  % (15809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.66  % (15809)Termination reason: Refutation
% 2.24/0.66  
% 2.24/0.66  % (15809)Memory used [KB]: 2942
% 2.24/0.66  % (15809)Time elapsed: 0.176 s
% 2.24/0.66  % (15809)------------------------------
% 2.24/0.66  % (15809)------------------------------
% 2.24/0.66  % (15801)Success in time 0.297 s
%------------------------------------------------------------------------------
