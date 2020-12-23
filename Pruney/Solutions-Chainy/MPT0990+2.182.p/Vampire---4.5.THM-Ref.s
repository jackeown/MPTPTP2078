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
% DateTime   : Thu Dec  3 13:03:00 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  236 (1366 expanded)
%              Number of leaves         :   30 ( 430 expanded)
%              Depth                    :   30
%              Number of atoms          :  888 (12812 expanded)
%              Number of equality atoms :  218 (4348 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f324,f349,f365,f487,f695,f713,f1266])).

fof(f1266,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1265])).

fof(f1265,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1264,f87])).

fof(f87,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f71,f70])).

fof(f70,plain,
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

fof(f71,plain,
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
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
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
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

fof(f1264,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1258,f267])).

fof(f267,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(backward_demodulation,[],[f178,f265])).

fof(f265,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f264,f140])).

fof(f140,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f120,f113])).

fof(f113,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f120,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f264,plain,(
    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f263,f202])).

fof(f202,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f201,f76])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f201,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f200,f77])).

fof(f77,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f200,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f199,f78])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

fof(f199,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f198,f84])).

fof(f84,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f198,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f192,f86])).

fof(f86,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f72])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f88,f82])).

fof(f82,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f263,plain,(
    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f157,f169])).

fof(f169,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f166,f127])).

fof(f127,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f166,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f78,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f157,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f149,f76])).

fof(f149,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f84,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f178,plain,(
    sK2 = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) ),
    inference(resolution,[],[f169,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f118,f113])).

fof(f118,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1258,plain,
    ( sK3 = k2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(superposition,[],[f386,f1253])).

fof(f1253,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1252,f827])).

fof(f827,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f183,f826])).

fof(f826,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f825,f140])).

fof(f825,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f757,f319])).

fof(f319,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl5_1
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f757,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f756,f176])).

fof(f176,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f173,f127])).

fof(f173,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f81,f126])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

fof(f756,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f744,f79])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f744,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f322,f93])).

fof(f322,plain,
    ( v2_funct_1(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl5_2
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f183,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f176,f137])).

fof(f1252,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1247,f207])).

fof(f207,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f206,f76])).

fof(f206,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f205,f77])).

fof(f205,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f204,f78])).

fof(f204,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f203,f84])).

fof(f203,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f191,f86])).

fof(f191,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f89,f82])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1247,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f1018,f329])).

fof(f329,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl5_3
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1018,plain,
    ( ! [X18] :
        ( ~ v1_relat_1(X18)
        | k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k6_partfun1(sK0)) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1002,f486])).

fof(f486,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl5_7
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1002,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k5_relat_1(sK2,sK3)) ) ),
    inference(resolution,[],[f180,f176])).

fof(f180,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X3,sK2),X2) = k5_relat_1(X3,k5_relat_1(sK2,X2)) ) ),
    inference(resolution,[],[f169,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f386,plain,(
    ! [X1] : k2_funct_1(k5_relat_1(k6_partfun1(X1),sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X1)) ),
    inference(forward_demodulation,[],[f385,f134])).

fof(f134,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f102,f113,f113])).

fof(f102,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f385,plain,(
    ! [X1] : k2_funct_1(k5_relat_1(k6_partfun1(X1),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X1))) ),
    inference(subsumption_resolution,[],[f384,f142])).

fof(f142,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f128,f113])).

fof(f128,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f384,plain,(
    ! [X1] :
      ( k2_funct_1(k5_relat_1(k6_partfun1(X1),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X1)))
      | ~ v1_relat_1(k6_partfun1(X1)) ) ),
    inference(subsumption_resolution,[],[f380,f141])).

fof(f141,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f129,f113])).

fof(f129,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f380,plain,(
    ! [X1] :
      ( k2_funct_1(k5_relat_1(k6_partfun1(X1),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X1)))
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1)) ) ),
    inference(resolution,[],[f376,f135])).

fof(f135,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f109,f113])).

fof(f109,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f376,plain,(
    ! [X1] :
      ( ~ v2_funct_1(X1)
      | k2_funct_1(k5_relat_1(X1,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f156,f169])).

fof(f156,plain,(
    ! [X1] :
      ( ~ v2_funct_1(X1)
      | k2_funct_1(k5_relat_1(X1,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f148,f76])).

fof(f148,plain,(
    ! [X1] :
      ( ~ v2_funct_1(X1)
      | k2_funct_1(k5_relat_1(X1,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f84,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f713,plain,
    ( spl5_2
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f710,f135])).

fof(f710,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl5_2
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f583,f486])).

fof(f583,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl5_2 ),
    inference(forward_demodulation,[],[f582,f403])).

fof(f403,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f398,f79])).

fof(f398,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f167,f81])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK2,X0) = k1_partfun1(sK0,sK1,X1,X2,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f164,f76])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK2,X0) = k1_partfun1(sK0,sK1,X1,X2,sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f78,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f582,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f581,f79])).

fof(f581,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f580,f85])).

fof(f85,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f72])).

fof(f580,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f579,f81])).

fof(f579,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f576,f323])).

fof(f323,plain,
    ( ~ v2_funct_1(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f321])).

fof(f576,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f197,f80])).

fof(f80,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f197,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,sK1,X2)
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f196,f76])).

fof(f196,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f195,f77])).

fof(f195,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f193,f78])).

fof(f193,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,(
    ! [X2,X3] :
      ( sK1 != sK1
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f105,f82])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f695,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f694])).

fof(f694,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f693,f76])).

fof(f693,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f692,f78])).

fof(f692,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f691,f333])).

fof(f333,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl5_4
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f691,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f690,f630])).

fof(f630,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f629,f329])).

fof(f629,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f280,f333])).

fof(f280,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f278,f254])).

fof(f254,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f253,f238])).

fof(f238,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f163,f82])).

fof(f163,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f78,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f253,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f159,f169])).

fof(f159,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f151,f76])).

fof(f151,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f84,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f278,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f125,f266])).

fof(f266,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f258,f265])).

fof(f258,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f160,f169])).

fof(f160,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f76])).

fof(f152,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f84,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f125,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f690,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f689,f482])).

fof(f482,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl5_6
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f689,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f115,f643])).

fof(f643,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f642,f202])).

fof(f642,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f634,f333])).

fof(f634,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f630,f167])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f487,plain,
    ( ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f451,f484,f480])).

fof(f451,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(global_subsumption,[],[f449,f450])).

fof(f450,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f438,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f438,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f83,f403])).

fof(f83,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f449,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f448,f76])).

fof(f448,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f447,f78])).

fof(f447,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f446,f79])).

fof(f446,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f441,f81])).

fof(f441,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f115,f403])).

fof(f365,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f363,f169])).

fof(f363,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f358,f76])).

fof(f358,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(resolution,[],[f334,f98])).

fof(f98,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f334,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f332])).

fof(f349,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f347,f169])).

fof(f347,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f342,f76])).

fof(f342,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(resolution,[],[f330,f97])).

fof(f97,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f330,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f328])).

fof(f324,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f233,f321,f317])).

fof(f233,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f232,f79])).

fof(f232,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f231,f80])).

fof(f231,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f230,f81])).

fof(f230,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f221,f85])).

fof(f221,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f88,f215])).

fof(f215,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f214,f79])).

fof(f214,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f213,f80])).

fof(f213,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f212,f81])).

fof(f212,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f211,f76])).

fof(f211,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f210,f77])).

fof(f210,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f209,f78])).

fof(f209,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f83,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (989)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (982)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.51  % (977)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (980)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (972)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (970)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (971)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (982)Refutation not found, incomplete strategy% (982)------------------------------
% 0.22/0.52  % (982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (996)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (982)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (982)Memory used [KB]: 10746
% 0.22/0.52  % (982)Time elapsed: 0.104 s
% 0.22/0.52  % (982)------------------------------
% 0.22/0.52  % (982)------------------------------
% 0.22/0.52  % (975)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (969)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.54  % (965)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.26/0.54  % (984)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.26/0.54  % (967)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.54  % (997)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.26/0.54  % (998)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.55  % (990)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.48/0.55  % (974)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.48/0.55  % (995)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.55  % (986)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.55  % (988)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.55  % (994)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.55  % (981)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.55  % (973)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.56  % (976)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.56  % (978)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.56  % (966)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.48/0.56  % (979)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.48/0.56  % (987)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.57  % (993)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.57  % (983)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.01/0.63  % (993)Refutation found. Thanks to Tanya!
% 2.01/0.63  % SZS status Theorem for theBenchmark
% 2.01/0.65  % SZS output start Proof for theBenchmark
% 2.01/0.65  fof(f1267,plain,(
% 2.01/0.65    $false),
% 2.01/0.65    inference(avatar_sat_refutation,[],[f324,f349,f365,f487,f695,f713,f1266])).
% 2.01/0.65  fof(f1266,plain,(
% 2.01/0.65    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_7),
% 2.01/0.65    inference(avatar_contradiction_clause,[],[f1265])).
% 2.01/0.65  fof(f1265,plain,(
% 2.01/0.65    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_7)),
% 2.01/0.65    inference(subsumption_resolution,[],[f1264,f87])).
% 2.01/0.65  fof(f87,plain,(
% 2.01/0.65    k2_funct_1(sK2) != sK3),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f72,plain,(
% 2.01/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.01/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f71,f70])).
% 2.01/0.65  fof(f70,plain,(
% 2.01/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.01/0.65    introduced(choice_axiom,[])).
% 2.01/0.65  fof(f71,plain,(
% 2.01/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.01/0.65    introduced(choice_axiom,[])).
% 2.01/0.65  fof(f36,plain,(
% 2.01/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.01/0.65    inference(flattening,[],[f35])).
% 2.01/0.65  fof(f35,plain,(
% 2.01/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.01/0.65    inference(ennf_transformation,[],[f34])).
% 2.01/0.65  fof(f34,negated_conjecture,(
% 2.01/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.01/0.65    inference(negated_conjecture,[],[f33])).
% 2.01/0.65  fof(f33,conjecture,(
% 2.01/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.01/0.65  fof(f1264,plain,(
% 2.01/0.65    k2_funct_1(sK2) = sK3 | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_7)),
% 2.01/0.65    inference(forward_demodulation,[],[f1258,f267])).
% 2.01/0.65  fof(f267,plain,(
% 2.01/0.65    sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 2.01/0.65    inference(backward_demodulation,[],[f178,f265])).
% 2.01/0.65  fof(f265,plain,(
% 2.01/0.65    sK0 = k1_relat_1(sK2)),
% 2.01/0.65    inference(forward_demodulation,[],[f264,f140])).
% 2.01/0.65  fof(f140,plain,(
% 2.01/0.65    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.01/0.65    inference(definition_unfolding,[],[f120,f113])).
% 2.01/0.65  fof(f113,plain,(
% 2.01/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f28])).
% 2.01/0.65  fof(f28,axiom,(
% 2.01/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.01/0.65  fof(f120,plain,(
% 2.01/0.65    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.01/0.65    inference(cnf_transformation,[],[f10])).
% 2.01/0.65  fof(f10,axiom,(
% 2.01/0.65    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.01/0.65  fof(f264,plain,(
% 2.01/0.65    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 2.01/0.65    inference(forward_demodulation,[],[f263,f202])).
% 2.01/0.65  fof(f202,plain,(
% 2.01/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.01/0.65    inference(subsumption_resolution,[],[f201,f76])).
% 2.01/0.65  fof(f76,plain,(
% 2.01/0.65    v1_funct_1(sK2)),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f201,plain,(
% 2.01/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f200,f77])).
% 2.01/0.65  fof(f77,plain,(
% 2.01/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f200,plain,(
% 2.01/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f199,f78])).
% 2.01/0.65  fof(f78,plain,(
% 2.01/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f199,plain,(
% 2.01/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f198,f84])).
% 2.01/0.65  fof(f84,plain,(
% 2.01/0.65    v2_funct_1(sK2)),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f198,plain,(
% 2.01/0.65    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f192,f86])).
% 2.01/0.65  fof(f86,plain,(
% 2.01/0.65    k1_xboole_0 != sK1),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f192,plain,(
% 2.01/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(trivial_inequality_removal,[],[f189])).
% 2.01/0.65  fof(f189,plain,(
% 2.01/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(superposition,[],[f88,f82])).
% 2.01/0.65  fof(f82,plain,(
% 2.01/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f88,plain,(
% 2.01/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f38])).
% 2.01/0.65  fof(f38,plain,(
% 2.01/0.65    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.01/0.65    inference(flattening,[],[f37])).
% 2.01/0.65  fof(f37,plain,(
% 2.01/0.65    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.01/0.65    inference(ennf_transformation,[],[f31])).
% 2.01/0.65  fof(f31,axiom,(
% 2.01/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.01/0.65  fof(f263,plain,(
% 2.01/0.65    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 2.01/0.65    inference(subsumption_resolution,[],[f157,f169])).
% 2.01/0.65  fof(f169,plain,(
% 2.01/0.65    v1_relat_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f166,f127])).
% 2.01/0.65  fof(f127,plain,(
% 2.01/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.01/0.65    inference(cnf_transformation,[],[f6])).
% 2.01/0.65  fof(f6,axiom,(
% 2.01/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.01/0.65  fof(f166,plain,(
% 2.01/0.65    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.01/0.65    inference(resolution,[],[f78,f126])).
% 2.01/0.65  fof(f126,plain,(
% 2.01/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f68])).
% 2.01/0.65  fof(f68,plain,(
% 2.01/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.01/0.65    inference(ennf_transformation,[],[f5])).
% 2.01/0.65  fof(f5,axiom,(
% 2.01/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.01/0.65  fof(f157,plain,(
% 2.01/0.65    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f149,f76])).
% 2.01/0.65  fof(f149,plain,(
% 2.01/0.65    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.01/0.65    inference(resolution,[],[f84,f93])).
% 2.01/0.65  fof(f93,plain,(
% 2.01/0.65    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f44])).
% 2.01/0.65  fof(f44,plain,(
% 2.01/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.65    inference(flattening,[],[f43])).
% 2.01/0.65  fof(f43,plain,(
% 2.01/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.65    inference(ennf_transformation,[],[f19])).
% 2.01/0.65  fof(f19,axiom,(
% 2.01/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 2.01/0.65  fof(f178,plain,(
% 2.01/0.65    sK2 = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2)),
% 2.01/0.65    inference(resolution,[],[f169,f137])).
% 2.01/0.65  fof(f137,plain,(
% 2.01/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 2.01/0.65    inference(definition_unfolding,[],[f118,f113])).
% 2.01/0.65  fof(f118,plain,(
% 2.01/0.65    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f63])).
% 2.01/0.65  fof(f63,plain,(
% 2.01/0.65    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.01/0.65    inference(ennf_transformation,[],[f11])).
% 2.01/0.65  fof(f11,axiom,(
% 2.01/0.65    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 2.01/0.65  fof(f1258,plain,(
% 2.01/0.65    sK3 = k2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_7)),
% 2.01/0.65    inference(superposition,[],[f386,f1253])).
% 2.01/0.65  fof(f1253,plain,(
% 2.01/0.65    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_7)),
% 2.01/0.65    inference(forward_demodulation,[],[f1252,f827])).
% 2.01/0.65  fof(f827,plain,(
% 2.01/0.65    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl5_1 | ~spl5_2)),
% 2.01/0.65    inference(backward_demodulation,[],[f183,f826])).
% 2.01/0.65  fof(f826,plain,(
% 2.01/0.65    sK1 = k1_relat_1(sK3) | (~spl5_1 | ~spl5_2)),
% 2.01/0.65    inference(forward_demodulation,[],[f825,f140])).
% 2.01/0.65  fof(f825,plain,(
% 2.01/0.65    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) | (~spl5_1 | ~spl5_2)),
% 2.01/0.65    inference(forward_demodulation,[],[f757,f319])).
% 2.01/0.65  fof(f319,plain,(
% 2.01/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl5_1),
% 2.01/0.65    inference(avatar_component_clause,[],[f317])).
% 2.01/0.65  fof(f317,plain,(
% 2.01/0.65    spl5_1 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.01/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.01/0.65  fof(f757,plain,(
% 2.01/0.65    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~spl5_2),
% 2.01/0.65    inference(subsumption_resolution,[],[f756,f176])).
% 2.01/0.65  fof(f176,plain,(
% 2.01/0.65    v1_relat_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f173,f127])).
% 2.01/0.65  fof(f173,plain,(
% 2.01/0.65    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.01/0.65    inference(resolution,[],[f81,f126])).
% 2.01/0.65  fof(f81,plain,(
% 2.01/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f756,plain,(
% 2.01/0.65    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(sK3) | ~spl5_2),
% 2.01/0.65    inference(subsumption_resolution,[],[f744,f79])).
% 2.01/0.65  fof(f79,plain,(
% 2.01/0.65    v1_funct_1(sK3)),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f744,plain,(
% 2.01/0.65    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_2),
% 2.01/0.65    inference(resolution,[],[f322,f93])).
% 2.01/0.65  fof(f322,plain,(
% 2.01/0.65    v2_funct_1(sK3) | ~spl5_2),
% 2.01/0.65    inference(avatar_component_clause,[],[f321])).
% 2.01/0.65  fof(f321,plain,(
% 2.01/0.65    spl5_2 <=> v2_funct_1(sK3)),
% 2.01/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.01/0.65  fof(f183,plain,(
% 2.01/0.65    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 2.01/0.65    inference(resolution,[],[f176,f137])).
% 2.01/0.65  fof(f1252,plain,(
% 2.01/0.65    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl5_3 | ~spl5_7)),
% 2.01/0.65    inference(forward_demodulation,[],[f1247,f207])).
% 2.01/0.65  fof(f207,plain,(
% 2.01/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.01/0.65    inference(subsumption_resolution,[],[f206,f76])).
% 2.01/0.65  fof(f206,plain,(
% 2.01/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f205,f77])).
% 2.01/0.65  fof(f205,plain,(
% 2.01/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f204,f78])).
% 2.01/0.65  fof(f204,plain,(
% 2.01/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f203,f84])).
% 2.01/0.65  fof(f203,plain,(
% 2.01/0.65    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f191,f86])).
% 2.01/0.65  fof(f191,plain,(
% 2.01/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(trivial_inequality_removal,[],[f190])).
% 2.01/0.65  fof(f190,plain,(
% 2.01/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(superposition,[],[f89,f82])).
% 2.01/0.65  fof(f89,plain,(
% 2.01/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f38])).
% 2.01/0.65  fof(f1247,plain,(
% 2.01/0.65    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | (~spl5_3 | ~spl5_7)),
% 2.01/0.65    inference(resolution,[],[f1018,f329])).
% 2.01/0.65  fof(f329,plain,(
% 2.01/0.65    v1_relat_1(k2_funct_1(sK2)) | ~spl5_3),
% 2.01/0.65    inference(avatar_component_clause,[],[f328])).
% 2.01/0.65  fof(f328,plain,(
% 2.01/0.65    spl5_3 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.01/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.01/0.65  fof(f1018,plain,(
% 2.01/0.65    ( ! [X18] : (~v1_relat_1(X18) | k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k6_partfun1(sK0))) ) | ~spl5_7),
% 2.01/0.65    inference(forward_demodulation,[],[f1002,f486])).
% 2.01/0.65  fof(f486,plain,(
% 2.01/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl5_7),
% 2.01/0.65    inference(avatar_component_clause,[],[f484])).
% 2.01/0.65  fof(f484,plain,(
% 2.01/0.65    spl5_7 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.01/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.01/0.65  fof(f1002,plain,(
% 2.01/0.65    ( ! [X18] : (~v1_relat_1(X18) | k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k5_relat_1(sK2,sK3))) )),
% 2.01/0.65    inference(resolution,[],[f180,f176])).
% 2.01/0.65  fof(f180,plain,(
% 2.01/0.65    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,sK2),X2) = k5_relat_1(X3,k5_relat_1(sK2,X2))) )),
% 2.01/0.65    inference(resolution,[],[f169,f117])).
% 2.01/0.65  fof(f117,plain,(
% 2.01/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.01/0.65    inference(cnf_transformation,[],[f62])).
% 2.01/0.65  fof(f62,plain,(
% 2.01/0.65    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.01/0.65    inference(ennf_transformation,[],[f9])).
% 2.01/0.65  fof(f9,axiom,(
% 2.01/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.01/0.65  fof(f386,plain,(
% 2.01/0.65    ( ! [X1] : (k2_funct_1(k5_relat_1(k6_partfun1(X1),sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X1))) )),
% 2.01/0.65    inference(forward_demodulation,[],[f385,f134])).
% 2.01/0.65  fof(f134,plain,(
% 2.01/0.65    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 2.01/0.65    inference(definition_unfolding,[],[f102,f113,f113])).
% 2.01/0.65  fof(f102,plain,(
% 2.01/0.65    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.01/0.65    inference(cnf_transformation,[],[f22])).
% 2.01/0.65  fof(f22,axiom,(
% 2.01/0.65    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 2.01/0.65  fof(f385,plain,(
% 2.01/0.65    ( ! [X1] : (k2_funct_1(k5_relat_1(k6_partfun1(X1),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X1)))) )),
% 2.01/0.65    inference(subsumption_resolution,[],[f384,f142])).
% 2.01/0.65  fof(f142,plain,(
% 2.01/0.65    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.01/0.65    inference(definition_unfolding,[],[f128,f113])).
% 2.01/0.65  fof(f128,plain,(
% 2.01/0.65    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.01/0.65    inference(cnf_transformation,[],[f14])).
% 2.01/0.65  fof(f14,axiom,(
% 2.01/0.65    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.01/0.65  fof(f384,plain,(
% 2.01/0.65    ( ! [X1] : (k2_funct_1(k5_relat_1(k6_partfun1(X1),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X1))) | ~v1_relat_1(k6_partfun1(X1))) )),
% 2.01/0.65    inference(subsumption_resolution,[],[f380,f141])).
% 2.01/0.65  fof(f141,plain,(
% 2.01/0.65    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 2.01/0.65    inference(definition_unfolding,[],[f129,f113])).
% 2.01/0.65  fof(f129,plain,(
% 2.01/0.65    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.01/0.65    inference(cnf_transformation,[],[f14])).
% 2.01/0.65  fof(f380,plain,(
% 2.01/0.65    ( ! [X1] : (k2_funct_1(k5_relat_1(k6_partfun1(X1),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X1))) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1))) )),
% 2.01/0.65    inference(resolution,[],[f376,f135])).
% 2.01/0.65  fof(f135,plain,(
% 2.01/0.65    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.01/0.65    inference(definition_unfolding,[],[f109,f113])).
% 2.01/0.65  fof(f109,plain,(
% 2.01/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.01/0.65    inference(cnf_transformation,[],[f15])).
% 2.01/0.65  fof(f15,axiom,(
% 2.01/0.65    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.01/0.65  fof(f376,plain,(
% 2.01/0.65    ( ! [X1] : (~v2_funct_1(X1) | k2_funct_1(k5_relat_1(X1,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.01/0.65    inference(subsumption_resolution,[],[f156,f169])).
% 2.01/0.65  fof(f156,plain,(
% 2.01/0.65    ( ! [X1] : (~v2_funct_1(X1) | k2_funct_1(k5_relat_1(X1,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X1)) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.01/0.65    inference(subsumption_resolution,[],[f148,f76])).
% 2.01/0.65  fof(f148,plain,(
% 2.01/0.65    ( ! [X1] : (~v2_funct_1(X1) | k2_funct_1(k5_relat_1(X1,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.01/0.65    inference(resolution,[],[f84,f90])).
% 2.01/0.65  fof(f90,plain,(
% 2.01/0.65    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v2_funct_1(X0) | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f40])).
% 2.01/0.65  fof(f40,plain,(
% 2.01/0.65    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.65    inference(flattening,[],[f39])).
% 2.01/0.65  fof(f39,plain,(
% 2.01/0.65    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.65    inference(ennf_transformation,[],[f21])).
% 2.01/0.65  fof(f21,axiom,(
% 2.01/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).
% 2.01/0.65  fof(f713,plain,(
% 2.01/0.65    spl5_2 | ~spl5_7),
% 2.01/0.65    inference(avatar_contradiction_clause,[],[f712])).
% 2.01/0.65  fof(f712,plain,(
% 2.01/0.65    $false | (spl5_2 | ~spl5_7)),
% 2.01/0.65    inference(subsumption_resolution,[],[f710,f135])).
% 2.01/0.65  fof(f710,plain,(
% 2.01/0.65    ~v2_funct_1(k6_partfun1(sK0)) | (spl5_2 | ~spl5_7)),
% 2.01/0.65    inference(backward_demodulation,[],[f583,f486])).
% 2.01/0.65  fof(f583,plain,(
% 2.01/0.65    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl5_2),
% 2.01/0.65    inference(forward_demodulation,[],[f582,f403])).
% 2.01/0.65  fof(f403,plain,(
% 2.01/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f398,f79])).
% 2.01/0.65  fof(f398,plain,(
% 2.01/0.65    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.01/0.65    inference(resolution,[],[f167,f81])).
% 2.01/0.65  fof(f167,plain,(
% 2.01/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK2,X0) = k1_partfun1(sK0,sK1,X1,X2,sK2,X0)) )),
% 2.01/0.65    inference(subsumption_resolution,[],[f164,f76])).
% 2.01/0.65  fof(f164,plain,(
% 2.01/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK2,X0) = k1_partfun1(sK0,sK1,X1,X2,sK2,X0) | ~v1_funct_1(sK2)) )),
% 2.01/0.65    inference(resolution,[],[f78,f116])).
% 2.01/0.65  fof(f116,plain,(
% 2.01/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f61])).
% 2.01/0.65  fof(f61,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.01/0.65    inference(flattening,[],[f60])).
% 2.01/0.65  fof(f60,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.01/0.65    inference(ennf_transformation,[],[f27])).
% 2.01/0.65  fof(f27,axiom,(
% 2.01/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.01/0.65  fof(f582,plain,(
% 2.01/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl5_2),
% 2.01/0.65    inference(subsumption_resolution,[],[f581,f79])).
% 2.01/0.65  fof(f581,plain,(
% 2.01/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~v1_funct_1(sK3) | spl5_2),
% 2.01/0.65    inference(subsumption_resolution,[],[f580,f85])).
% 2.01/0.65  fof(f85,plain,(
% 2.01/0.65    k1_xboole_0 != sK0),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f580,plain,(
% 2.01/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl5_2),
% 2.01/0.65    inference(subsumption_resolution,[],[f579,f81])).
% 2.01/0.65  fof(f579,plain,(
% 2.01/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl5_2),
% 2.01/0.65    inference(subsumption_resolution,[],[f576,f323])).
% 2.01/0.65  fof(f323,plain,(
% 2.01/0.65    ~v2_funct_1(sK3) | spl5_2),
% 2.01/0.65    inference(avatar_component_clause,[],[f321])).
% 2.01/0.65  fof(f576,plain,(
% 2.01/0.65    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(resolution,[],[f197,f80])).
% 2.01/0.65  fof(f80,plain,(
% 2.01/0.65    v1_funct_2(sK3,sK1,sK0)),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f197,plain,(
% 2.01/0.65    ( ! [X2,X3] : (~v1_funct_2(X3,sK1,X2) | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 2.01/0.65    inference(subsumption_resolution,[],[f196,f76])).
% 2.01/0.65  fof(f196,plain,(
% 2.01/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_1(sK2)) )),
% 2.01/0.65    inference(subsumption_resolution,[],[f195,f77])).
% 2.01/0.65  fof(f195,plain,(
% 2.01/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.01/0.65    inference(subsumption_resolution,[],[f193,f78])).
% 2.01/0.65  fof(f193,plain,(
% 2.01/0.65    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.01/0.65    inference(trivial_inequality_removal,[],[f188])).
% 2.01/0.65  fof(f188,plain,(
% 2.01/0.65    ( ! [X2,X3] : (sK1 != sK1 | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.01/0.65    inference(superposition,[],[f105,f82])).
% 2.01/0.65  fof(f105,plain,(
% 2.01/0.65    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f52])).
% 2.01/0.65  fof(f52,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.01/0.65    inference(flattening,[],[f51])).
% 2.01/0.65  fof(f51,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.01/0.65    inference(ennf_transformation,[],[f30])).
% 2.01/0.65  fof(f30,axiom,(
% 2.01/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 2.01/0.65  fof(f695,plain,(
% 2.01/0.65    ~spl5_3 | ~spl5_4 | spl5_6),
% 2.01/0.65    inference(avatar_contradiction_clause,[],[f694])).
% 2.01/0.65  fof(f694,plain,(
% 2.01/0.65    $false | (~spl5_3 | ~spl5_4 | spl5_6)),
% 2.01/0.65    inference(subsumption_resolution,[],[f693,f76])).
% 2.01/0.65  fof(f693,plain,(
% 2.01/0.65    ~v1_funct_1(sK2) | (~spl5_3 | ~spl5_4 | spl5_6)),
% 2.01/0.65    inference(subsumption_resolution,[],[f692,f78])).
% 2.01/0.65  fof(f692,plain,(
% 2.01/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_3 | ~spl5_4 | spl5_6)),
% 2.01/0.65    inference(subsumption_resolution,[],[f691,f333])).
% 2.01/0.65  fof(f333,plain,(
% 2.01/0.65    v1_funct_1(k2_funct_1(sK2)) | ~spl5_4),
% 2.01/0.65    inference(avatar_component_clause,[],[f332])).
% 2.01/0.65  fof(f332,plain,(
% 2.01/0.65    spl5_4 <=> v1_funct_1(k2_funct_1(sK2))),
% 2.01/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.01/0.65  fof(f691,plain,(
% 2.01/0.65    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_3 | ~spl5_4 | spl5_6)),
% 2.01/0.65    inference(subsumption_resolution,[],[f690,f630])).
% 2.01/0.65  fof(f630,plain,(
% 2.01/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_3 | ~spl5_4)),
% 2.01/0.65    inference(subsumption_resolution,[],[f629,f329])).
% 2.01/0.65  fof(f629,plain,(
% 2.01/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_4),
% 2.01/0.65    inference(subsumption_resolution,[],[f280,f333])).
% 2.01/0.65  fof(f280,plain,(
% 2.01/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 2.01/0.65    inference(forward_demodulation,[],[f278,f254])).
% 2.01/0.65  fof(f254,plain,(
% 2.01/0.65    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 2.01/0.65    inference(forward_demodulation,[],[f253,f238])).
% 2.01/0.65  fof(f238,plain,(
% 2.01/0.65    sK1 = k2_relat_1(sK2)),
% 2.01/0.65    inference(forward_demodulation,[],[f163,f82])).
% 2.01/0.65  fof(f163,plain,(
% 2.01/0.65    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.01/0.65    inference(resolution,[],[f78,f122])).
% 2.01/0.65  fof(f122,plain,(
% 2.01/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f65])).
% 2.01/0.65  fof(f65,plain,(
% 2.01/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.65    inference(ennf_transformation,[],[f23])).
% 2.01/0.65  fof(f23,axiom,(
% 2.01/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.01/0.65  fof(f253,plain,(
% 2.01/0.65    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 2.01/0.65    inference(subsumption_resolution,[],[f159,f169])).
% 2.01/0.65  fof(f159,plain,(
% 2.01/0.65    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f151,f76])).
% 2.01/0.65  fof(f151,plain,(
% 2.01/0.65    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.01/0.65    inference(resolution,[],[f84,f95])).
% 2.01/0.65  fof(f95,plain,(
% 2.01/0.65    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f46])).
% 2.01/0.65  fof(f46,plain,(
% 2.01/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.65    inference(flattening,[],[f45])).
% 2.01/0.65  fof(f45,plain,(
% 2.01/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.65    inference(ennf_transformation,[],[f18])).
% 2.01/0.65  fof(f18,axiom,(
% 2.01/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.01/0.65  fof(f278,plain,(
% 2.01/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 2.01/0.65    inference(superposition,[],[f125,f266])).
% 2.01/0.65  fof(f266,plain,(
% 2.01/0.65    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 2.01/0.65    inference(backward_demodulation,[],[f258,f265])).
% 2.01/0.65  fof(f258,plain,(
% 2.01/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.01/0.65    inference(subsumption_resolution,[],[f160,f169])).
% 2.01/0.65  fof(f160,plain,(
% 2.01/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f152,f76])).
% 2.01/0.65  fof(f152,plain,(
% 2.01/0.65    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.01/0.65    inference(resolution,[],[f84,f96])).
% 2.01/0.65  fof(f96,plain,(
% 2.01/0.65    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f46])).
% 2.01/0.65  fof(f125,plain,(
% 2.01/0.65    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f67])).
% 2.01/0.65  fof(f67,plain,(
% 2.01/0.65    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.65    inference(flattening,[],[f66])).
% 2.01/0.65  fof(f66,plain,(
% 2.01/0.65    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.65    inference(ennf_transformation,[],[f32])).
% 2.01/0.65  fof(f32,axiom,(
% 2.01/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 2.01/0.65  fof(f690,plain,(
% 2.01/0.65    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_3 | ~spl5_4 | spl5_6)),
% 2.01/0.65    inference(subsumption_resolution,[],[f689,f482])).
% 2.01/0.65  fof(f482,plain,(
% 2.01/0.65    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_6),
% 2.01/0.65    inference(avatar_component_clause,[],[f480])).
% 2.01/0.65  fof(f480,plain,(
% 2.01/0.65    spl5_6 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.01/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.01/0.65  fof(f689,plain,(
% 2.01/0.65    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_3 | ~spl5_4)),
% 2.01/0.65    inference(superposition,[],[f115,f643])).
% 2.01/0.65  fof(f643,plain,(
% 2.01/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl5_3 | ~spl5_4)),
% 2.01/0.65    inference(forward_demodulation,[],[f642,f202])).
% 2.01/0.65  fof(f642,plain,(
% 2.01/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl5_3 | ~spl5_4)),
% 2.01/0.65    inference(subsumption_resolution,[],[f634,f333])).
% 2.01/0.65  fof(f634,plain,(
% 2.01/0.65    ~v1_funct_1(k2_funct_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl5_3 | ~spl5_4)),
% 2.01/0.65    inference(resolution,[],[f630,f167])).
% 2.01/0.65  fof(f115,plain,(
% 2.01/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f59])).
% 2.01/0.65  fof(f59,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.01/0.65    inference(flattening,[],[f58])).
% 2.01/0.65  fof(f58,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.01/0.65    inference(ennf_transformation,[],[f25])).
% 2.01/0.65  fof(f25,axiom,(
% 2.01/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.01/0.65  fof(f487,plain,(
% 2.01/0.65    ~spl5_6 | spl5_7),
% 2.01/0.65    inference(avatar_split_clause,[],[f451,f484,f480])).
% 2.01/0.65  fof(f451,plain,(
% 2.01/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.01/0.65    inference(global_subsumption,[],[f449,f450])).
% 2.01/0.65  fof(f450,plain,(
% 2.01/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.01/0.65    inference(resolution,[],[f438,f110])).
% 2.01/0.65  fof(f110,plain,(
% 2.01/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/0.65    inference(cnf_transformation,[],[f73])).
% 2.01/0.65  fof(f73,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.65    inference(nnf_transformation,[],[f55])).
% 2.01/0.65  fof(f55,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.65    inference(flattening,[],[f54])).
% 2.01/0.65  fof(f54,plain,(
% 2.01/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.01/0.65    inference(ennf_transformation,[],[f24])).
% 2.01/0.65  fof(f24,axiom,(
% 2.01/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.01/0.65  fof(f438,plain,(
% 2.01/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.01/0.65    inference(backward_demodulation,[],[f83,f403])).
% 2.01/0.65  fof(f83,plain,(
% 2.01/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.01/0.65    inference(cnf_transformation,[],[f72])).
% 2.01/0.65  fof(f449,plain,(
% 2.01/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.01/0.65    inference(subsumption_resolution,[],[f448,f76])).
% 2.01/0.65  fof(f448,plain,(
% 2.01/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f447,f78])).
% 2.01/0.65  fof(f447,plain,(
% 2.01/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f446,f79])).
% 2.01/0.65  fof(f446,plain,(
% 2.01/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(subsumption_resolution,[],[f441,f81])).
% 2.01/0.65  fof(f441,plain,(
% 2.01/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.01/0.65    inference(superposition,[],[f115,f403])).
% 2.01/0.65  fof(f365,plain,(
% 2.01/0.65    spl5_4),
% 2.01/0.65    inference(avatar_contradiction_clause,[],[f364])).
% 2.01/0.65  fof(f364,plain,(
% 2.01/0.65    $false | spl5_4),
% 2.01/0.65    inference(subsumption_resolution,[],[f363,f169])).
% 2.01/0.65  fof(f363,plain,(
% 2.01/0.65    ~v1_relat_1(sK2) | spl5_4),
% 2.01/0.65    inference(subsumption_resolution,[],[f358,f76])).
% 2.01/0.65  fof(f358,plain,(
% 2.01/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_4),
% 2.01/0.65    inference(resolution,[],[f334,f98])).
% 2.01/0.65  fof(f98,plain,(
% 2.01/0.65    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f48])).
% 2.01/0.65  fof(f48,plain,(
% 2.01/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.65    inference(flattening,[],[f47])).
% 2.01/0.65  fof(f47,plain,(
% 2.01/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.65    inference(ennf_transformation,[],[f13])).
% 2.01/0.65  fof(f13,axiom,(
% 2.01/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.01/0.65  fof(f334,plain,(
% 2.01/0.65    ~v1_funct_1(k2_funct_1(sK2)) | spl5_4),
% 2.01/0.65    inference(avatar_component_clause,[],[f332])).
% 2.01/0.65  fof(f349,plain,(
% 2.01/0.65    spl5_3),
% 2.01/0.65    inference(avatar_contradiction_clause,[],[f348])).
% 2.01/0.65  fof(f348,plain,(
% 2.01/0.65    $false | spl5_3),
% 2.01/0.65    inference(subsumption_resolution,[],[f347,f169])).
% 2.01/0.65  fof(f347,plain,(
% 2.01/0.65    ~v1_relat_1(sK2) | spl5_3),
% 2.01/0.65    inference(subsumption_resolution,[],[f342,f76])).
% 2.01/0.65  fof(f342,plain,(
% 2.01/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_3),
% 2.01/0.65    inference(resolution,[],[f330,f97])).
% 2.01/0.65  fof(f97,plain,(
% 2.01/0.65    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f48])).
% 2.01/0.65  fof(f330,plain,(
% 2.01/0.65    ~v1_relat_1(k2_funct_1(sK2)) | spl5_3),
% 2.01/0.65    inference(avatar_component_clause,[],[f328])).
% 2.01/0.65  fof(f324,plain,(
% 2.01/0.65    spl5_1 | ~spl5_2),
% 2.01/0.65    inference(avatar_split_clause,[],[f233,f321,f317])).
% 2.01/0.65  fof(f233,plain,(
% 2.01/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.01/0.65    inference(subsumption_resolution,[],[f232,f79])).
% 2.01/0.65  fof(f232,plain,(
% 2.01/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f231,f80])).
% 2.01/0.65  fof(f231,plain,(
% 2.01/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f230,f81])).
% 2.01/0.65  fof(f230,plain,(
% 2.01/0.65    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f221,f85])).
% 2.01/0.65  fof(f221,plain,(
% 2.01/0.65    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(trivial_inequality_removal,[],[f218])).
% 2.01/0.65  fof(f218,plain,(
% 2.01/0.65    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(superposition,[],[f88,f215])).
% 2.01/0.65  fof(f215,plain,(
% 2.01/0.65    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f214,f79])).
% 2.01/0.65  fof(f214,plain,(
% 2.01/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f213,f80])).
% 2.01/0.65  fof(f213,plain,(
% 2.01/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f212,f81])).
% 2.01/0.65  fof(f212,plain,(
% 2.01/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f211,f76])).
% 2.01/0.65  fof(f211,plain,(
% 2.01/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f210,f77])).
% 2.01/0.65  fof(f210,plain,(
% 2.01/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(subsumption_resolution,[],[f209,f78])).
% 2.01/0.65  fof(f209,plain,(
% 2.01/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.01/0.65    inference(resolution,[],[f83,f112])).
% 2.01/0.65  fof(f112,plain,(
% 2.01/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.01/0.65    inference(cnf_transformation,[],[f57])).
% 2.01/0.65  fof(f57,plain,(
% 2.01/0.65    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.01/0.65    inference(flattening,[],[f56])).
% 2.01/0.65  fof(f56,plain,(
% 2.01/0.65    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.01/0.65    inference(ennf_transformation,[],[f29])).
% 2.01/0.65  fof(f29,axiom,(
% 2.01/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.01/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.01/0.65  % SZS output end Proof for theBenchmark
% 2.01/0.65  % (993)------------------------------
% 2.01/0.65  % (993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.65  % (993)Termination reason: Refutation
% 2.01/0.65  
% 2.01/0.65  % (993)Memory used [KB]: 11385
% 2.01/0.65  % (993)Time elapsed: 0.215 s
% 2.01/0.65  % (993)------------------------------
% 2.01/0.65  % (993)------------------------------
% 2.01/0.66  % (953)Success in time 0.294 s
%------------------------------------------------------------------------------
