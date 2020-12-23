%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0989+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:01 EST 2020

% Result     : Theorem 3.52s
% Output     : Refutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 208 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 (1291 expanded)
%              Number of equality atoms :  109 ( 628 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8000,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7744,f7995])).

fof(f7995,plain,(
    k6_relat_1(sK38) = k5_relat_1(k4_relat_1(sK39),sK39) ),
    inference(subsumption_resolution,[],[f7739,f5827])).

fof(f5827,plain,(
    v1_relat_1(sK39) ),
    inference(resolution,[],[f3542,f4063])).

fof(f4063,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1894])).

fof(f1894,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3542,plain,(
    m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK37,sK38))) ),
    inference(cnf_transformation,[],[f2697])).

fof(f2697,plain,
    ( ( k6_partfun1(sK38) != k5_relat_1(k2_funct_1(sK39),sK39)
      | k6_partfun1(sK37) != k5_relat_1(sK39,k2_funct_1(sK39)) )
    & k1_xboole_0 != sK38
    & v2_funct_1(sK39)
    & sK38 = k2_relset_1(sK37,sK38,sK39)
    & m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK37,sK38)))
    & v1_funct_2(sK39,sK37,sK38)
    & v1_funct_1(sK39) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK37,sK38,sK39])],[f1545,f2696])).

fof(f2696,plain,
    ( ? [X0,X1,X2] :
        ( ( k6_partfun1(X1) != k5_relat_1(k2_funct_1(X2),X2)
          | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
        & k1_xboole_0 != X1
        & v2_funct_1(X2)
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( k6_partfun1(sK38) != k5_relat_1(k2_funct_1(sK39),sK39)
        | k6_partfun1(sK37) != k5_relat_1(sK39,k2_funct_1(sK39)) )
      & k1_xboole_0 != sK38
      & v2_funct_1(sK39)
      & sK38 = k2_relset_1(sK37,sK38,sK39)
      & m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK37,sK38)))
      & v1_funct_2(sK39,sK37,sK38)
      & v1_funct_1(sK39) ) ),
    introduced(choice_axiom,[])).

fof(f1545,plain,(
    ? [X0,X1,X2] :
      ( ( k6_partfun1(X1) != k5_relat_1(k2_funct_1(X2),X2)
        | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
      & k1_xboole_0 != X1
      & v2_funct_1(X2)
      & k2_relset_1(X0,X1,X2) = X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1544])).

fof(f1544,plain,(
    ? [X0,X1,X2] :
      ( ( k6_partfun1(X1) != k5_relat_1(k2_funct_1(X2),X2)
        | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
      & k1_xboole_0 != X1
      & v2_funct_1(X2)
      & k2_relset_1(X0,X1,X2) = X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1510])).

fof(f1510,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & k2_relset_1(X0,X1,X2) = X1 )
         => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
              & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1509])).

fof(f1509,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f7739,plain,
    ( k6_relat_1(sK38) = k5_relat_1(k4_relat_1(sK39),sK39)
    | ~ v1_relat_1(sK39) ),
    inference(backward_demodulation,[],[f5937,f7732])).

fof(f7732,plain,(
    k2_funct_1(sK39) = k4_relat_1(sK39) ),
    inference(resolution,[],[f5780,f5827])).

fof(f5780,plain,
    ( ~ v1_relat_1(sK39)
    | k2_funct_1(sK39) = k4_relat_1(sK39) ),
    inference(subsumption_resolution,[],[f5758,f3540])).

fof(f3540,plain,(
    v1_funct_1(sK39) ),
    inference(cnf_transformation,[],[f2697])).

fof(f5758,plain,
    ( k2_funct_1(sK39) = k4_relat_1(sK39)
    | ~ v1_funct_1(sK39)
    | ~ v1_relat_1(sK39) ),
    inference(resolution,[],[f3544,f3715])).

fof(f3715,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1697])).

fof(f1697,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1696])).

fof(f1696,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f906])).

fof(f906,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f3544,plain,(
    v2_funct_1(sK39) ),
    inference(cnf_transformation,[],[f2697])).

fof(f5937,plain,
    ( k5_relat_1(k2_funct_1(sK39),sK39) = k6_relat_1(sK38)
    | ~ v1_relat_1(sK39) ),
    inference(backward_demodulation,[],[f5769,f5931])).

fof(f5931,plain,(
    sK38 = k2_relat_1(sK39) ),
    inference(forward_demodulation,[],[f5812,f3543])).

fof(f3543,plain,(
    sK38 = k2_relset_1(sK37,sK38,sK39) ),
    inference(cnf_transformation,[],[f2697])).

fof(f5812,plain,(
    k2_relset_1(sK37,sK38,sK39) = k2_relat_1(sK39) ),
    inference(resolution,[],[f3542,f4040])).

fof(f4040,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1870])).

fof(f1870,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f5769,plain,
    ( k5_relat_1(k2_funct_1(sK39),sK39) = k6_relat_1(k2_relat_1(sK39))
    | ~ v1_relat_1(sK39) ),
    inference(subsumption_resolution,[],[f5747,f3540])).

fof(f5747,plain,
    ( k5_relat_1(k2_funct_1(sK39),sK39) = k6_relat_1(k2_relat_1(sK39))
    | ~ v1_funct_1(sK39)
    | ~ v1_relat_1(sK39) ),
    inference(resolution,[],[f3544,f3648])).

fof(f3648,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1642])).

fof(f1642,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1641])).

fof(f1641,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1032])).

fof(f1032,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f7744,plain,(
    k6_relat_1(sK38) != k5_relat_1(k4_relat_1(sK39),sK39) ),
    inference(backward_demodulation,[],[f6011,f7732])).

fof(f6011,plain,(
    k5_relat_1(k2_funct_1(sK39),sK39) != k6_relat_1(sK38) ),
    inference(trivial_inequality_removal,[],[f6010])).

fof(f6010,plain,
    ( k6_relat_1(sK37) != k6_relat_1(sK37)
    | k5_relat_1(k2_funct_1(sK39),sK39) != k6_relat_1(sK38) ),
    inference(backward_demodulation,[],[f5702,f6009])).

fof(f6009,plain,(
    k5_relat_1(sK39,k2_funct_1(sK39)) = k6_relat_1(sK37) ),
    inference(subsumption_resolution,[],[f5986,f5827])).

fof(f5986,plain,
    ( k5_relat_1(sK39,k2_funct_1(sK39)) = k6_relat_1(sK37)
    | ~ v1_relat_1(sK39) ),
    inference(backward_demodulation,[],[f5768,f5976])).

fof(f5976,plain,(
    sK37 = k1_relat_1(sK39) ),
    inference(forward_demodulation,[],[f5860,f5958])).

fof(f5958,plain,(
    sK37 = k1_relset_1(sK37,sK38,sK39) ),
    inference(subsumption_resolution,[],[f5957,f3545])).

fof(f3545,plain,(
    k1_xboole_0 != sK38 ),
    inference(cnf_transformation,[],[f2697])).

fof(f5957,plain,
    ( k1_xboole_0 = sK38
    | sK37 = k1_relset_1(sK37,sK38,sK39) ),
    inference(subsumption_resolution,[],[f5836,f3541])).

fof(f3541,plain,(
    v1_funct_2(sK39,sK37,sK38) ),
    inference(cnf_transformation,[],[f2697])).

fof(f5836,plain,
    ( ~ v1_funct_2(sK39,sK37,sK38)
    | k1_xboole_0 = sK38
    | sK37 = k1_relset_1(sK37,sK38,sK39) ),
    inference(resolution,[],[f3542,f4211])).

fof(f4211,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f2971])).

fof(f2971,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f1958])).

fof(f1958,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1957])).

fof(f1957,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1472])).

fof(f1472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f5860,plain,(
    k1_relat_1(sK39) = k1_relset_1(sK37,sK38,sK39) ),
    inference(resolution,[],[f3542,f5367])).

fof(f5367,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2573])).

fof(f2573,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f5768,plain,
    ( k5_relat_1(sK39,k2_funct_1(sK39)) = k6_relat_1(k1_relat_1(sK39))
    | ~ v1_relat_1(sK39) ),
    inference(subsumption_resolution,[],[f5746,f3540])).

fof(f5746,plain,
    ( k5_relat_1(sK39,k2_funct_1(sK39)) = k6_relat_1(k1_relat_1(sK39))
    | ~ v1_funct_1(sK39)
    | ~ v1_relat_1(sK39) ),
    inference(resolution,[],[f3544,f3647])).

fof(f3647,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1642])).

fof(f5702,plain,
    ( k5_relat_1(sK39,k2_funct_1(sK39)) != k6_relat_1(sK37)
    | k5_relat_1(k2_funct_1(sK39),sK39) != k6_relat_1(sK38) ),
    inference(forward_demodulation,[],[f5701,f3731])).

fof(f3731,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f1487])).

fof(f1487,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f5701,plain,
    ( k5_relat_1(k2_funct_1(sK39),sK39) != k6_relat_1(sK38)
    | k6_partfun1(sK37) != k5_relat_1(sK39,k2_funct_1(sK39)) ),
    inference(forward_demodulation,[],[f3546,f3731])).

fof(f3546,plain,
    ( k6_partfun1(sK38) != k5_relat_1(k2_funct_1(sK39),sK39)
    | k6_partfun1(sK37) != k5_relat_1(sK39,k2_funct_1(sK39)) ),
    inference(cnf_transformation,[],[f2697])).
%------------------------------------------------------------------------------
