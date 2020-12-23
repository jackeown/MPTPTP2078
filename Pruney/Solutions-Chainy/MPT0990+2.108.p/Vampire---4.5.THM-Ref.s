%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:47 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 910 expanded)
%              Number of leaves         :   24 ( 259 expanded)
%              Depth                    :   20
%              Number of atoms          :  452 (7383 expanded)
%              Number of equality atoms :  143 (2772 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1665,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1664,f84])).

fof(f84,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f69,f68])).

fof(f68,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
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

fof(f1664,plain,(
    k2_funct_1(sK2) = sK3 ),
    inference(backward_demodulation,[],[f719,f1663])).

fof(f1663,plain,(
    sK3 = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f1503,f1546])).

fof(f1546,plain,(
    sK3 = k5_relat_1(k6_relat_1(sK1),sK3) ),
    inference(backward_demodulation,[],[f190,f1543])).

fof(f1543,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1542,f434])).

fof(f434,plain,(
    sK1 = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f433,f201])).

fof(f201,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f198,f79])).

fof(f79,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f198,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f116,f76])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f433,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f163,f240])).

fof(f240,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f238,f136])).

fof(f136,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f133,f106])).

fof(f106,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f133,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f96,f76])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f238,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f158,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f158,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f117,f76])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f163,plain,(
    ! [X5] : k2_relat_1(k7_relat_1(sK2,X5)) = k9_relat_1(sK2,X5) ),
    inference(resolution,[],[f107,f136])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1542,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f1487,f89])).

fof(f89,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1487,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f468,f1480])).

fof(f1480,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f1137,f1080])).

fof(f1080,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f1078,f1075])).

fof(f1075,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f554,f78])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f70])).

fof(f554,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) ) ),
    inference(resolution,[],[f322,f76])).

fof(f322,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f245,f75])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f245,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f120,f77])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f64])).

% (27166)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f1078,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f237,f1075])).

fof(f237,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f236,f128])).

fof(f128,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f88,f85])).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f236,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f118,f127])).

fof(f127,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f80,f85])).

fof(f80,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1137,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f1135,f1075])).

fof(f1135,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f562,f78])).

fof(f562,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f328,f76])).

fof(f328,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f247,f75])).

fof(f247,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f122,f77])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
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

fof(f468,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(backward_demodulation,[],[f374,f466])).

fof(f466,plain,(
    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(resolution,[],[f196,f136])).

fof(f196,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k1_relat_1(k5_relat_1(X6,sK3)) = k10_relat_1(X6,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f94,f137])).

fof(f137,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f134,f106])).

fof(f134,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f96,f78])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f374,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(resolution,[],[f251,f224])).

fof(f224,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f223,f201])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f221,f136])).

fof(f221,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f111,f75])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f251,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f249,f137])).

fof(f249,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f159,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f159,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f117,f78])).

fof(f190,plain,(
    sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f137,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1503,plain,(
    k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3) ),
    inference(backward_demodulation,[],[f794,f1480])).

fof(f794,plain,(
    k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_relat_1(sK1),sK3) ),
    inference(forward_demodulation,[],[f786,f218])).

fof(f218,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    inference(forward_demodulation,[],[f217,f201])).

fof(f217,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f216,f136])).

fof(f216,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f214,f75])).

fof(f214,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f786,plain,(
    k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) ),
    inference(resolution,[],[f484,f153])).

fof(f153,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f136,f129])).

fof(f129,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f99,f75])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f484,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(X9,sK2),sK3) = k5_relat_1(X9,k5_relat_1(sK2,sK3)) ) ),
    inference(resolution,[],[f229,f136])).

fof(f229,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X10)
      | k5_relat_1(k5_relat_1(X9,X10),sK3) = k5_relat_1(X9,k5_relat_1(X10,sK3))
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f95,f137])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f719,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) ),
    inference(resolution,[],[f269,f241])).

fof(f241,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f239,f136])).

fof(f239,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f158,f109])).

fof(f269,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(sK2),X4)
      | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(X4)) ) ),
    inference(forward_demodulation,[],[f261,f180])).

fof(f180,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f179,f136])).

fof(f179,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f177,f75])).

fof(f177,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f102,f81])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f261,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X4)
      | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(X4)) ) ),
    inference(resolution,[],[f153,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (27148)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (27140)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (27130)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (27132)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (27128)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (27135)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (27134)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (27145)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (27143)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (27127)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (27131)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (27129)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (27138)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (27136)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (27125)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (27151)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (27153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (27126)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (27144)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (27147)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (27149)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (27154)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (27137)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (27141)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (27146)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (27150)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (27139)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (27141)Refutation not found, incomplete strategy% (27141)------------------------------
% 0.22/0.55  % (27141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27141)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27141)Memory used [KB]: 10746
% 0.22/0.55  % (27141)Time elapsed: 0.139 s
% 0.22/0.55  % (27141)------------------------------
% 0.22/0.55  % (27141)------------------------------
% 0.22/0.55  % (27133)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (27142)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.57  % (27152)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.20/0.68  % (27132)Refutation found. Thanks to Tanya!
% 2.20/0.68  % SZS status Theorem for theBenchmark
% 2.20/0.68  % SZS output start Proof for theBenchmark
% 2.20/0.68  fof(f1665,plain,(
% 2.20/0.68    $false),
% 2.20/0.68    inference(subsumption_resolution,[],[f1664,f84])).
% 2.20/0.68  fof(f84,plain,(
% 2.20/0.68    k2_funct_1(sK2) != sK3),
% 2.20/0.68    inference(cnf_transformation,[],[f70])).
% 2.20/0.68  fof(f70,plain,(
% 2.20/0.68    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 2.20/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f69,f68])).
% 2.20/0.68  fof(f68,plain,(
% 2.20/0.68    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 2.20/0.68    introduced(choice_axiom,[])).
% 2.20/0.68  fof(f69,plain,(
% 2.20/0.68    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3))),
% 2.20/0.68    introduced(choice_axiom,[])).
% 2.20/0.68  fof(f35,plain,(
% 2.20/0.68    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.20/0.68    inference(flattening,[],[f34])).
% 2.20/0.68  fof(f34,plain,(
% 2.20/0.68    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.20/0.68    inference(ennf_transformation,[],[f30])).
% 2.20/0.68  fof(f30,plain,(
% 2.20/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.20/0.68    inference(pure_predicate_removal,[],[f29])).
% 2.20/0.68  fof(f29,negated_conjecture,(
% 2.20/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.20/0.68    inference(negated_conjecture,[],[f28])).
% 2.20/0.68  fof(f28,conjecture,(
% 2.20/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.20/0.68  fof(f1664,plain,(
% 2.20/0.68    k2_funct_1(sK2) = sK3),
% 2.20/0.68    inference(backward_demodulation,[],[f719,f1663])).
% 2.20/0.68  fof(f1663,plain,(
% 2.20/0.68    sK3 = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))),
% 2.20/0.68    inference(forward_demodulation,[],[f1503,f1546])).
% 2.20/0.68  fof(f1546,plain,(
% 2.20/0.68    sK3 = k5_relat_1(k6_relat_1(sK1),sK3)),
% 2.20/0.68    inference(backward_demodulation,[],[f190,f1543])).
% 2.20/0.68  fof(f1543,plain,(
% 2.20/0.68    sK1 = k1_relat_1(sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f1542,f434])).
% 2.20/0.68  fof(f434,plain,(
% 2.20/0.68    sK1 = k9_relat_1(sK2,sK0)),
% 2.20/0.68    inference(forward_demodulation,[],[f433,f201])).
% 2.20/0.68  fof(f201,plain,(
% 2.20/0.68    sK1 = k2_relat_1(sK2)),
% 2.20/0.68    inference(forward_demodulation,[],[f198,f79])).
% 2.20/0.68  fof(f79,plain,(
% 2.20/0.68    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.20/0.68    inference(cnf_transformation,[],[f70])).
% 2.20/0.68  fof(f198,plain,(
% 2.20/0.68    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.20/0.68    inference(resolution,[],[f116,f76])).
% 2.20/0.68  fof(f76,plain,(
% 2.20/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.20/0.68    inference(cnf_transformation,[],[f70])).
% 2.20/0.68  fof(f116,plain,(
% 2.20/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f60])).
% 2.20/0.68  fof(f60,plain,(
% 2.20/0.68    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.68    inference(ennf_transformation,[],[f21])).
% 2.20/0.68  fof(f21,axiom,(
% 2.20/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.20/0.68  fof(f433,plain,(
% 2.20/0.68    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 2.20/0.68    inference(superposition,[],[f163,f240])).
% 2.20/0.68  fof(f240,plain,(
% 2.20/0.68    sK2 = k7_relat_1(sK2,sK0)),
% 2.20/0.68    inference(subsumption_resolution,[],[f238,f136])).
% 2.20/0.68  fof(f136,plain,(
% 2.20/0.68    v1_relat_1(sK2)),
% 2.20/0.68    inference(subsumption_resolution,[],[f133,f106])).
% 2.20/0.68  fof(f106,plain,(
% 2.20/0.68    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.20/0.68    inference(cnf_transformation,[],[f4])).
% 2.20/0.68  fof(f4,axiom,(
% 2.20/0.68    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.20/0.68  fof(f133,plain,(
% 2.20/0.68    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.20/0.68    inference(resolution,[],[f96,f76])).
% 2.20/0.68  fof(f96,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f41])).
% 2.20/0.68  fof(f41,plain,(
% 2.20/0.68    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.20/0.68    inference(ennf_transformation,[],[f2])).
% 2.20/0.68  fof(f2,axiom,(
% 2.20/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.20/0.68  fof(f238,plain,(
% 2.20/0.68    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 2.20/0.68    inference(resolution,[],[f158,f112])).
% 2.20/0.68  fof(f112,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f59])).
% 2.20/0.68  fof(f59,plain,(
% 2.20/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.20/0.68    inference(flattening,[],[f58])).
% 2.20/0.68  fof(f58,plain,(
% 2.20/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.20/0.68    inference(ennf_transformation,[],[f9])).
% 2.20/0.68  fof(f9,axiom,(
% 2.20/0.68    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.20/0.68  fof(f158,plain,(
% 2.20/0.68    v4_relat_1(sK2,sK0)),
% 2.20/0.68    inference(resolution,[],[f117,f76])).
% 2.20/0.68  fof(f117,plain,(
% 2.20/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f61])).
% 2.20/0.68  fof(f61,plain,(
% 2.20/0.68    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.68    inference(ennf_transformation,[],[f33])).
% 2.20/0.68  fof(f33,plain,(
% 2.20/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.20/0.68    inference(pure_predicate_removal,[],[f20])).
% 2.20/0.68  fof(f20,axiom,(
% 2.20/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.20/0.68  fof(f163,plain,(
% 2.20/0.68    ( ! [X5] : (k2_relat_1(k7_relat_1(sK2,X5)) = k9_relat_1(sK2,X5)) )),
% 2.20/0.68    inference(resolution,[],[f107,f136])).
% 2.20/0.68  fof(f107,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f52])).
% 2.20/0.68  fof(f52,plain,(
% 2.20/0.68    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.20/0.68    inference(ennf_transformation,[],[f6])).
% 2.20/0.68  fof(f6,axiom,(
% 2.20/0.68    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.20/0.68  fof(f1542,plain,(
% 2.20/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 2.20/0.68    inference(forward_demodulation,[],[f1487,f89])).
% 2.20/0.68  fof(f89,plain,(
% 2.20/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.20/0.68    inference(cnf_transformation,[],[f11])).
% 2.20/0.68  fof(f11,axiom,(
% 2.20/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.20/0.68  fof(f1487,plain,(
% 2.20/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_relat_1(sK0)))),
% 2.20/0.68    inference(backward_demodulation,[],[f468,f1480])).
% 2.20/0.68  fof(f1480,plain,(
% 2.20/0.68    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.20/0.68    inference(resolution,[],[f1137,f1080])).
% 2.20/0.68  fof(f1080,plain,(
% 2.20/0.68    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f1078,f1075])).
% 2.20/0.68  fof(f1075,plain,(
% 2.20/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.20/0.68    inference(resolution,[],[f554,f78])).
% 2.20/0.68  fof(f78,plain,(
% 2.20/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.20/0.68    inference(cnf_transformation,[],[f70])).
% 2.20/0.68  fof(f554,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3)) )),
% 2.20/0.68    inference(resolution,[],[f322,f76])).
% 2.20/0.68  fof(f322,plain,(
% 2.20/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.20/0.68    inference(resolution,[],[f245,f75])).
% 2.20/0.68  fof(f75,plain,(
% 2.20/0.68    v1_funct_1(sK2)),
% 2.20/0.68    inference(cnf_transformation,[],[f70])).
% 2.20/0.68  fof(f245,plain,(
% 2.20/0.68    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 2.20/0.68    inference(resolution,[],[f120,f77])).
% 2.20/0.68  fof(f77,plain,(
% 2.20/0.68    v1_funct_1(sK3)),
% 2.20/0.68    inference(cnf_transformation,[],[f70])).
% 2.20/0.68  fof(f120,plain,(
% 2.20/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f65])).
% 2.20/0.68  fof(f65,plain,(
% 2.20/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.20/0.68    inference(flattening,[],[f64])).
% 2.20/0.68  % (27166)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.20/0.68  fof(f64,plain,(
% 2.20/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.20/0.68    inference(ennf_transformation,[],[f25])).
% 2.20/0.68  fof(f25,axiom,(
% 2.20/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.20/0.68  fof(f1078,plain,(
% 2.20/0.68    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.20/0.68    inference(backward_demodulation,[],[f237,f1075])).
% 2.20/0.68  fof(f237,plain,(
% 2.20/0.68    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.20/0.68    inference(subsumption_resolution,[],[f236,f128])).
% 2.20/0.68  fof(f128,plain,(
% 2.20/0.68    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.20/0.68    inference(forward_demodulation,[],[f88,f85])).
% 2.20/0.68  fof(f85,plain,(
% 2.20/0.68    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f26])).
% 2.20/0.68  fof(f26,axiom,(
% 2.20/0.68    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.20/0.68  fof(f88,plain,(
% 2.20/0.68    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.20/0.68    inference(cnf_transformation,[],[f32])).
% 2.20/0.68  fof(f32,plain,(
% 2.20/0.68    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.20/0.68    inference(pure_predicate_removal,[],[f24])).
% 2.20/0.68  fof(f24,axiom,(
% 2.20/0.68    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.20/0.68  fof(f236,plain,(
% 2.20/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.20/0.68    inference(resolution,[],[f118,f127])).
% 2.20/0.68  fof(f127,plain,(
% 2.20/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.20/0.68    inference(forward_demodulation,[],[f80,f85])).
% 2.20/0.68  fof(f80,plain,(
% 2.20/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.20/0.68    inference(cnf_transformation,[],[f70])).
% 2.20/0.68  fof(f118,plain,(
% 2.20/0.68    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.68    inference(cnf_transformation,[],[f74])).
% 2.20/0.68  fof(f74,plain,(
% 2.20/0.68    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.68    inference(nnf_transformation,[],[f63])).
% 2.20/0.68  fof(f63,plain,(
% 2.20/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.68    inference(flattening,[],[f62])).
% 2.20/0.68  fof(f62,plain,(
% 2.20/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.20/0.68    inference(ennf_transformation,[],[f22])).
% 2.20/0.68  fof(f22,axiom,(
% 2.20/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.20/0.68  fof(f1137,plain,(
% 2.20/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.20/0.68    inference(forward_demodulation,[],[f1135,f1075])).
% 2.20/0.68  fof(f1135,plain,(
% 2.20/0.68    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.20/0.68    inference(resolution,[],[f562,f78])).
% 2.20/0.68  fof(f562,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 2.20/0.68    inference(resolution,[],[f328,f76])).
% 2.20/0.68  fof(f328,plain,(
% 2.20/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.20/0.68    inference(resolution,[],[f247,f75])).
% 2.20/0.68  fof(f247,plain,(
% 2.20/0.68    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 2.20/0.68    inference(resolution,[],[f122,f77])).
% 2.20/0.68  fof(f122,plain,(
% 2.20/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f67])).
% 2.20/0.68  fof(f67,plain,(
% 2.20/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.20/0.68    inference(flattening,[],[f66])).
% 2.20/0.68  fof(f66,plain,(
% 2.20/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.20/0.68    inference(ennf_transformation,[],[f23])).
% 2.20/0.68  fof(f23,axiom,(
% 2.20/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.20/0.68  fof(f468,plain,(
% 2.20/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 2.20/0.68    inference(backward_demodulation,[],[f374,f466])).
% 2.20/0.68  fof(f466,plain,(
% 2.20/0.68    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3))),
% 2.20/0.68    inference(resolution,[],[f196,f136])).
% 2.20/0.68  fof(f196,plain,(
% 2.20/0.68    ( ! [X6] : (~v1_relat_1(X6) | k1_relat_1(k5_relat_1(X6,sK3)) = k10_relat_1(X6,k1_relat_1(sK3))) )),
% 2.20/0.68    inference(resolution,[],[f94,f137])).
% 2.20/0.68  fof(f137,plain,(
% 2.20/0.68    v1_relat_1(sK3)),
% 2.20/0.68    inference(subsumption_resolution,[],[f134,f106])).
% 2.20/0.68  fof(f134,plain,(
% 2.20/0.68    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.20/0.68    inference(resolution,[],[f96,f78])).
% 2.20/0.68  fof(f94,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f39])).
% 2.20/0.68  fof(f39,plain,(
% 2.20/0.68    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.20/0.68    inference(ennf_transformation,[],[f8])).
% 2.20/0.68  fof(f8,axiom,(
% 2.20/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.20/0.68  fof(f374,plain,(
% 2.20/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))),
% 2.20/0.68    inference(resolution,[],[f251,f224])).
% 2.20/0.68  fof(f224,plain,(
% 2.20/0.68    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 2.20/0.68    inference(forward_demodulation,[],[f223,f201])).
% 2.20/0.68  fof(f223,plain,(
% 2.20/0.68    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 2.20/0.68    inference(subsumption_resolution,[],[f221,f136])).
% 2.20/0.68  fof(f221,plain,(
% 2.20/0.68    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 2.20/0.68    inference(resolution,[],[f111,f75])).
% 2.20/0.68  fof(f111,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f57])).
% 2.20/0.68  fof(f57,plain,(
% 2.20/0.68    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.20/0.68    inference(flattening,[],[f56])).
% 2.20/0.68  fof(f56,plain,(
% 2.20/0.68    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.20/0.68    inference(ennf_transformation,[],[f16])).
% 2.20/0.68  fof(f16,axiom,(
% 2.20/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.20/0.68  fof(f251,plain,(
% 2.20/0.68    r1_tarski(k1_relat_1(sK3),sK1)),
% 2.20/0.68    inference(subsumption_resolution,[],[f249,f137])).
% 2.20/0.68  fof(f249,plain,(
% 2.20/0.68    r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 2.20/0.68    inference(resolution,[],[f159,f109])).
% 2.20/0.68  fof(f109,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f71])).
% 2.20/0.68  fof(f71,plain,(
% 2.20/0.68    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.20/0.68    inference(nnf_transformation,[],[f55])).
% 2.20/0.68  fof(f55,plain,(
% 2.20/0.68    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.20/0.68    inference(ennf_transformation,[],[f3])).
% 2.20/0.68  fof(f3,axiom,(
% 2.20/0.68    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.20/0.68  fof(f159,plain,(
% 2.20/0.68    v4_relat_1(sK3,sK1)),
% 2.20/0.68    inference(resolution,[],[f117,f78])).
% 2.20/0.68  fof(f190,plain,(
% 2.20/0.68    sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)),
% 2.20/0.68    inference(resolution,[],[f137,f93])).
% 2.20/0.68  fof(f93,plain,(
% 2.20/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.20/0.68    inference(cnf_transformation,[],[f38])).
% 2.20/0.68  fof(f38,plain,(
% 2.20/0.68    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.20/0.68    inference(ennf_transformation,[],[f12])).
% 2.20/0.68  fof(f12,axiom,(
% 2.20/0.68    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.20/0.68  fof(f1503,plain,(
% 2.20/0.68    k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3)),
% 2.20/0.68    inference(backward_demodulation,[],[f794,f1480])).
% 2.20/0.68  fof(f794,plain,(
% 2.20/0.68    k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_relat_1(sK1),sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f786,f218])).
% 2.20/0.68  fof(f218,plain,(
% 2.20/0.68    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 2.20/0.68    inference(forward_demodulation,[],[f217,f201])).
% 2.20/0.68  fof(f217,plain,(
% 2.20/0.68    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 2.20/0.68    inference(subsumption_resolution,[],[f216,f136])).
% 2.20/0.68  fof(f216,plain,(
% 2.20/0.68    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.20/0.68    inference(subsumption_resolution,[],[f214,f75])).
% 2.20/0.68  fof(f214,plain,(
% 2.20/0.68    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.20/0.68    inference(resolution,[],[f104,f81])).
% 2.20/0.68  fof(f81,plain,(
% 2.20/0.68    v2_funct_1(sK2)),
% 2.20/0.68    inference(cnf_transformation,[],[f70])).
% 2.20/0.68  fof(f104,plain,(
% 2.20/0.68    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f49])).
% 2.20/0.68  fof(f49,plain,(
% 2.20/0.68    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.20/0.68    inference(flattening,[],[f48])).
% 2.20/0.68  fof(f48,plain,(
% 2.20/0.68    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.20/0.68    inference(ennf_transformation,[],[f19])).
% 2.20/0.68  fof(f19,axiom,(
% 2.20/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.20/0.68  fof(f786,plain,(
% 2.20/0.68    k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))),
% 2.20/0.68    inference(resolution,[],[f484,f153])).
% 2.20/0.68  fof(f153,plain,(
% 2.20/0.68    v1_relat_1(k2_funct_1(sK2))),
% 2.20/0.68    inference(resolution,[],[f136,f129])).
% 2.20/0.68  fof(f129,plain,(
% 2.20/0.68    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 2.20/0.68    inference(resolution,[],[f99,f75])).
% 2.20/0.68  fof(f99,plain,(
% 2.20/0.68    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f45])).
% 2.20/0.68  fof(f45,plain,(
% 2.20/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.20/0.68    inference(flattening,[],[f44])).
% 2.20/0.68  fof(f44,plain,(
% 2.20/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.20/0.68    inference(ennf_transformation,[],[f14])).
% 2.20/0.68  fof(f14,axiom,(
% 2.20/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.20/0.68  fof(f484,plain,(
% 2.20/0.68    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(k5_relat_1(X9,sK2),sK3) = k5_relat_1(X9,k5_relat_1(sK2,sK3))) )),
% 2.20/0.68    inference(resolution,[],[f229,f136])).
% 2.20/0.68  fof(f229,plain,(
% 2.20/0.68    ( ! [X10,X9] : (~v1_relat_1(X10) | k5_relat_1(k5_relat_1(X9,X10),sK3) = k5_relat_1(X9,k5_relat_1(X10,sK3)) | ~v1_relat_1(X9)) )),
% 2.20/0.68    inference(resolution,[],[f95,f137])).
% 2.20/0.68  fof(f95,plain,(
% 2.20/0.68    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f40])).
% 2.20/0.68  fof(f40,plain,(
% 2.20/0.68    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.20/0.68    inference(ennf_transformation,[],[f10])).
% 2.20/0.68  fof(f10,axiom,(
% 2.20/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.20/0.68  fof(f719,plain,(
% 2.20/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))),
% 2.20/0.68    inference(resolution,[],[f269,f241])).
% 2.20/0.68  fof(f241,plain,(
% 2.20/0.68    r1_tarski(k1_relat_1(sK2),sK0)),
% 2.20/0.68    inference(subsumption_resolution,[],[f239,f136])).
% 2.20/0.68  fof(f239,plain,(
% 2.20/0.68    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 2.20/0.68    inference(resolution,[],[f158,f109])).
% 2.20/0.68  fof(f269,plain,(
% 2.20/0.68    ( ! [X4] : (~r1_tarski(k1_relat_1(sK2),X4) | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(X4))) )),
% 2.20/0.68    inference(forward_demodulation,[],[f261,f180])).
% 2.20/0.68  fof(f180,plain,(
% 2.20/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.20/0.68    inference(subsumption_resolution,[],[f179,f136])).
% 2.20/0.68  fof(f179,plain,(
% 2.20/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.20/0.68    inference(subsumption_resolution,[],[f177,f75])).
% 2.20/0.68  fof(f177,plain,(
% 2.20/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.20/0.68    inference(resolution,[],[f102,f81])).
% 2.20/0.68  fof(f102,plain,(
% 2.20/0.68    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f47])).
% 2.20/0.68  fof(f47,plain,(
% 2.20/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.20/0.68    inference(flattening,[],[f46])).
% 2.20/0.68  fof(f46,plain,(
% 2.20/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.20/0.68    inference(ennf_transformation,[],[f18])).
% 2.20/0.68  fof(f18,axiom,(
% 2.20/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.20/0.68  fof(f261,plain,(
% 2.20/0.68    ( ! [X4] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X4) | k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(X4))) )),
% 2.20/0.68    inference(resolution,[],[f153,f108])).
% 2.20/0.68  fof(f108,plain,(
% 2.20/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 2.20/0.68    inference(cnf_transformation,[],[f54])).
% 2.20/0.68  fof(f54,plain,(
% 2.20/0.68    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.20/0.68    inference(flattening,[],[f53])).
% 2.20/0.68  fof(f53,plain,(
% 2.20/0.68    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.20/0.68    inference(ennf_transformation,[],[f13])).
% 2.20/0.68  fof(f13,axiom,(
% 2.20/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.20/0.68  % SZS output end Proof for theBenchmark
% 2.20/0.68  % (27132)------------------------------
% 2.20/0.68  % (27132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (27132)Termination reason: Refutation
% 2.20/0.68  
% 2.20/0.68  % (27132)Memory used [KB]: 4221
% 2.20/0.68  % (27132)Time elapsed: 0.214 s
% 2.20/0.68  % (27132)------------------------------
% 2.20/0.68  % (27132)------------------------------
% 2.20/0.69  % (27124)Success in time 0.326 s
%------------------------------------------------------------------------------
