%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:27 EST 2020

% Result     : Theorem 6.81s
% Output     : Refutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  222 (4726 expanded)
%              Number of leaves         :   29 (1363 expanded)
%              Depth                    :   54
%              Number of atoms          : 1038 (33486 expanded)
%              Number of equality atoms :  189 (1636 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4108,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f81,f3190,f142])).

fof(f142,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f3190,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f3182,f3186])).

fof(f3186,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f3185,f81])).

fof(f3185,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4))
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f3184,f139])).

fof(f139,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f3184,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK4))
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f3183,f3046])).

fof(f3046,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f2847,f147])).

fof(f147,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f134,f130])).

fof(f130,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f80,f82])).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f80,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f134,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f87,f82])).

fof(f87,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f2847,plain,(
    sK2 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f246,f2840])).

fof(f2840,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f2829,f76])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
    & v2_funct_1(sK3)
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f56,f55])).

fof(f55,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
          & v2_funct_1(sK3)
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
        & v2_funct_1(sK3)
        & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v1_funct_2(X2,sK2,sK2)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
      & v2_funct_1(sK3)
      & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f2829,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f2314,f142])).

fof(f2314,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f79,f2206])).

fof(f2206,plain,
    ( k6_partfun1(sK2) = sK4
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f2205,f139])).

fof(f2205,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f2204,f81])).

fof(f2204,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3))
    | sK3 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k6_partfun1(sK2) = sK4 ),
    inference(forward_demodulation,[],[f2136,f139])).

fof(f2136,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK3))
    | sK3 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k6_partfun1(sK2) = sK4 ),
    inference(superposition,[],[f167,f2128])).

fof(f2128,plain,
    ( k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f2127,f316])).

fof(f316,plain,(
    r2_relset_1(sK2,sK2,sK3,sK3) ),
    inference(backward_demodulation,[],[f77,f313])).

fof(f313,plain,(
    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f312,f74])).

fof(f74,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f312,plain,
    ( ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f311,f76])).

fof(f311,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f310,f71])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f310,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f304,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f304,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(resolution,[],[f128,f229])).

fof(f229,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f221,f73])).

fof(f221,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f124,f77])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f77,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f2127,plain,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK3)
    | k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4 ),
    inference(forward_demodulation,[],[f2126,f1565])).

fof(f1565,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK2),sK3) ),
    inference(resolution,[],[f1555,f73])).

fof(f1555,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | sK3 = k5_relat_1(k6_partfun1(sK2),sK3) ) ),
    inference(resolution,[],[f1535,f73])).

fof(f1535,plain,(
    ! [X26,X25] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | sK3 = k5_relat_1(k6_partfun1(sK2),sK3) ) ),
    inference(resolution,[],[f1524,f71])).

fof(f1524,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
      | k5_relat_1(k6_partfun1(sK2),X0) = X0 ) ),
    inference(resolution,[],[f1288,f86])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f1288,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X9)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X7)))
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X7)))
      | k5_relat_1(k6_partfun1(sK2),X6) = X6 ) ),
    inference(resolution,[],[f1278,f466])).

fof(f466,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X4)))
      | k5_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(resolution,[],[f338,f309])).

fof(f309,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f128,f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f338,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k5_relat_1(k6_partfun1(X1),X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(k6_partfun1(X1),X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f335])).

fof(f335,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(k6_partfun1(X1),X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(k5_relat_1(k6_partfun1(X1),X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f265,f124])).

fof(f265,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f264,f86])).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f106,f129])).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f1278,plain,(
    v1_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[],[f1270,f73])).

fof(f1270,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f1264,f73])).

fof(f1264,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f1262,f73])).

fof(f1262,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f1261,f249])).

fof(f249,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f203,f246])).

fof(f203,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f174,f71])).

fof(f174,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f91,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1261,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(forward_demodulation,[],[f1260,f246])).

fof(f1260,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f1259,f71])).

fof(f1259,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(trivial_inequality_removal,[],[f1255])).

fof(f1255,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != k2_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f1218,f157])).

fof(f157,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f90,f103])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1218,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(sK3,X5,X4)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relat_1(sK3) != X4
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f1217,f71])).

fof(f1217,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relat_1(sK3) != X4
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | ~ v1_funct_2(sK3,X5,X4)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f1212,f78])).

fof(f78,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f1212,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relat_1(sK3) != X4
      | ~ v2_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | ~ v1_funct_2(sK3,X5,X4)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f1209,f283])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relat_1(X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f110,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f1209,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f1208,f249])).

fof(f1208,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(forward_demodulation,[],[f1207,f246])).

fof(f1207,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f1206,f71])).

fof(f1206,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(trivial_inequality_removal,[],[f1202])).

fof(f1202,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != k2_relat_1(sK3)
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f980,f157])).

fof(f980,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ v1_funct_2(sK3,X27,X24)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(forward_demodulation,[],[f979,f246])).

fof(f979,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(subsumption_resolution,[],[f973,f71])).

fof(f973,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ v1_funct_1(sK3)
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(resolution,[],[f762,f78])).

fof(f762,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X2)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | k2_relat_1(X2) != X1
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f761])).

fof(f761,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(X2) != X1
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f570,f105])).

fof(f570,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X5,X6,X0) != X6
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f569])).

fof(f569,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f365,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f365,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f362,f103])).

fof(f362,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f289,f136])).

fof(f136,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f92,f82])).

fof(f92,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f289,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f127,f126])).

fof(f127,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2126,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f2125,f1278])).

fof(f2125,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f2116,f86])).

fof(f2116,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k6_partfun1(sK2) = sK4 ),
    inference(resolution,[],[f1979,f1285])).

fof(f1285,plain,(
    v1_funct_2(k6_partfun1(sK2),sK2,sK2) ),
    inference(resolution,[],[f1278,f159])).

fof(f159,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | v1_funct_2(k6_partfun1(X0),X0,X0) ) ),
    inference(forward_demodulation,[],[f158,f134])).

fof(f158,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(X0),k1_relat_1(k6_partfun1(X0)),X0)
      | ~ v1_funct_1(k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f155,f133])).

fof(f133,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f88,f82])).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | v1_funct_2(k6_partfun1(X0),k1_relat_1(k6_partfun1(X0)),k2_relat_1(k6_partfun1(X0))) ) ),
    inference(resolution,[],[f90,f132])).

fof(f132,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f83,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1979,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | ~ v1_funct_1(X0)
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f1978,f71])).

fof(f1978,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f1963,f73])).

fof(f1963,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f1962])).

fof(f1962,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f1631,f126])).

fof(f1631,plain,(
    ! [X8] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X8,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X8,sK2,sK2)
      | ~ v1_funct_1(X8)
      | sK4 = X8 ) ),
    inference(forward_demodulation,[],[f1630,f313])).

fof(f1630,plain,(
    ! [X8] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X8,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X8,sK2,sK2)
      | ~ v1_funct_1(X8)
      | sK4 = X8 ) ),
    inference(subsumption_resolution,[],[f1629,f74])).

fof(f1629,plain,(
    ! [X8] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X8,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X8,sK2,sK2)
      | ~ v1_funct_1(X8)
      | sK4 = X8 ) ),
    inference(subsumption_resolution,[],[f1617,f76])).

fof(f1617,plain,(
    ! [X8] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X8,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X8,sK2,sK2)
      | ~ v1_funct_1(X8)
      | sK4 = X8 ) ),
    inference(resolution,[],[f1041,f75])).

fof(f75,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f1041,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_2(X7,X5,sK2)
      | ~ r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | X6 = X7 ) ),
    inference(subsumption_resolution,[],[f1031,f73])).

fof(f1031,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X7,X5,sK2)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | X6 = X7 ) ),
    inference(duplicate_literal_removal,[],[f1029])).

fof(f1029,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X7,X5,sK2)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | k1_xboole_0 = sK2
      | X6 = X7 ) ),
    inference(resolution,[],[f869,f72])).

fof(f72,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f869,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ v1_funct_2(sK3,X19,X20)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_xboole_0 = X20
      | ~ r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X23,X21,X19)
      | ~ v1_funct_1(X23)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X22,X21,X19)
      | ~ v1_funct_1(X22)
      | k1_xboole_0 = X19
      | X22 = X23 ) ),
    inference(subsumption_resolution,[],[f867,f71])).

fof(f867,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ v1_funct_2(sK3,X19,X20)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_xboole_0 = X20
      | ~ r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X23,X21,X19)
      | ~ v1_funct_1(X23)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X22,X21,X19)
      | ~ v1_funct_1(X22)
      | k1_xboole_0 = X19
      | X22 = X23 ) ),
    inference(resolution,[],[f691,f78])).

fof(f691,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ v2_funct_1(X7)
      | ~ v1_funct_2(X7,X8,X9)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k1_xboole_0 = X9
      | ~ r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_funct_2(X12,X10,X8)
      | ~ v1_funct_1(X12)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_funct_2(X11,X10,X8)
      | ~ v1_funct_1(X11)
      | k1_xboole_0 = X8
      | X11 = X12 ) ),
    inference(duplicate_literal_removal,[],[f690])).

fof(f690,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(X7,X8,X9)
      | ~ v1_funct_1(X7)
      | ~ v2_funct_1(X7)
      | k1_xboole_0 = X9
      | ~ r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_funct_2(X12,X10,X8)
      | ~ v1_funct_1(X12)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_funct_2(X11,X10,X8)
      | ~ v1_funct_1(X11)
      | k1_xboole_0 = X8
      | X11 = X12
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) ) ),
    inference(resolution,[],[f371,f124])).

fof(f371,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_relset_1(X3,X0,X4,X5)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X1,X0,X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | k1_xboole_0 = X2
      | ~ r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X5,X3,X0)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X4,X3,X0)
      | ~ v1_funct_1(X4)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f234,f113])).

fof(f113,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X8,X6,X0)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X7,X6,X0)
      | ~ v1_funct_1(X7)
      | r2_relset_1(X6,X0,X7,X8) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
          & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1))
          & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0)
          & v1_funct_1(sK7(X0,X1,X2))
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0)
          & v1_funct_1(sK6(X0,X1,X2)) ) )
      & ( ! [X6,X7] :
            ( ! [X8] :
                ( r2_relset_1(X6,X0,X7,X8)
                | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
                | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
                | ~ v1_funct_2(X8,X6,X0)
                | ~ v1_funct_1(X8) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
            | ~ v1_funct_2(X7,X6,X0)
            | ~ v1_funct_1(X7) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f66,f68,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ? [X5] :
              ( ~ r2_relset_1(X3,X0,X4,X5)
              & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
              & v1_funct_2(X5,X3,X0)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
          & v1_funct_2(X4,X3,X0)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5)
            & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
            & v1_funct_2(X5,sK5(X0,X1,X2),X0)
            & v1_funct_1(X5) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
        & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0)
        & v1_funct_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5)
          & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(X5,sK5(X0,X1,X2),X0)
          & v1_funct_1(X5) )
     => ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
        & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0)
        & v1_funct_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X3,X0,X4,X5)
                & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                & v1_funct_2(X5,X3,X0)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            & v1_funct_2(X4,X3,X0)
            & v1_funct_1(X4) ) )
      & ( ! [X6,X7] :
            ( ! [X8] :
                ( r2_relset_1(X6,X0,X7,X8)
                | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
                | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
                | ~ v1_funct_2(X8,X6,X0)
                | ~ v1_funct_1(X8) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
            | ~ v1_funct_2(X7,X6,X0)
            | ~ v1_funct_1(X7) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ? [X3,X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X3,X0,X4,X5)
                & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                & v1_funct_2(X5,X3,X0)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            & v1_funct_2(X4,X3,X0)
            & v1_funct_1(X4) ) )
      & ( ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ! [X3,X4] :
          ( ! [X5] :
              ( r2_relset_1(X3,X0,X4,X5)
              | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
              | ~ v1_funct_2(X5,X3,X0)
              | ~ v1_funct_1(X5) )
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
          | ~ v1_funct_2(X4,X3,X0)
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f122,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v2_funct_1(X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v2_funct_1(X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v2_funct_1(X2) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X1,X2,X0] :
      ( ( v2_funct_1(X2)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f41,f53,f52])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) ) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) ) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ ( v2_funct_1(X2)
            <=> ! [X3,X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                    & v1_funct_2(X4,X3,X0)
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                        & v1_funct_2(X5,X3,X0)
                        & v1_funct_1(X5) )
                     => ( r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                       => r2_relset_1(X3,X0,X4,X5) ) ) ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).

fof(f167,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK3))
    | sK3 = k2_zfmisc_1(sK2,sK2) ),
    inference(resolution,[],[f164,f73])).

fof(f164,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | X1 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f154,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f154,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f97,f98])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f79,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f246,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f245,f71])).

fof(f245,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f242,f73])).

fof(f242,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f211,f72])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relat_1(X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f94,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f3183,plain,
    ( k1_xboole_0 = sK4
    | ~ m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4)) ),
    inference(forward_demodulation,[],[f3050,f139])).

fof(f3050,plain,
    ( sK4 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4)) ),
    inference(backward_demodulation,[],[f168,f3046])).

fof(f168,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4))
    | k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(resolution,[],[f164,f76])).

fof(f3182,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3049,f130])).

fof(f3049,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f79,f3046])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:51:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (23244)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (23256)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (23248)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (23249)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (23240)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (23246)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (23239)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (23245)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (23252)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (23241)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (23260)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (23257)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (23235)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (23262)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (23236)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (23234)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (23254)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (23247)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (23238)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (23258)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (23237)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (23263)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (23259)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (23250)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (23251)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (23250)Refutation not found, incomplete strategy% (23250)------------------------------
% 0.21/0.54  % (23250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23250)Memory used [KB]: 10746
% 0.21/0.54  % (23250)Time elapsed: 0.131 s
% 0.21/0.54  % (23250)------------------------------
% 0.21/0.54  % (23250)------------------------------
% 0.21/0.54  % (23242)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (23243)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (23261)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (23255)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (23253)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.17/0.65  % (23244)Refutation not found, incomplete strategy% (23244)------------------------------
% 2.17/0.65  % (23244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.65  % (23244)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.65  
% 2.17/0.65  % (23244)Memory used [KB]: 11769
% 2.17/0.65  % (23244)Time elapsed: 0.215 s
% 2.17/0.65  % (23244)------------------------------
% 2.17/0.65  % (23244)------------------------------
% 2.72/0.74  % (23264)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.17/0.78  % (23234)Refutation not found, incomplete strategy% (23234)------------------------------
% 3.17/0.78  % (23234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.78  % (23234)Termination reason: Refutation not found, incomplete strategy
% 3.17/0.78  
% 3.17/0.78  % (23234)Memory used [KB]: 2046
% 3.17/0.78  % (23234)Time elapsed: 0.344 s
% 3.17/0.78  % (23234)------------------------------
% 3.17/0.78  % (23234)------------------------------
% 3.17/0.80  % (23262)Refutation not found, incomplete strategy% (23262)------------------------------
% 3.17/0.80  % (23262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.80  % (23262)Termination reason: Refutation not found, incomplete strategy
% 3.17/0.80  
% 3.17/0.80  % (23262)Memory used [KB]: 12665
% 3.17/0.80  % (23262)Time elapsed: 0.396 s
% 3.17/0.80  % (23262)------------------------------
% 3.17/0.80  % (23262)------------------------------
% 3.17/0.81  % (23236)Time limit reached!
% 3.17/0.81  % (23236)------------------------------
% 3.17/0.81  % (23236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.81  % (23236)Termination reason: Time limit
% 3.17/0.81  % (23236)Termination phase: Saturation
% 3.17/0.81  
% 3.17/0.81  % (23236)Memory used [KB]: 6780
% 3.17/0.81  % (23236)Time elapsed: 0.400 s
% 3.17/0.81  % (23236)------------------------------
% 3.17/0.81  % (23236)------------------------------
% 3.17/0.81  % (23265)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.17/0.83  % (23258)Time limit reached!
% 3.17/0.83  % (23258)------------------------------
% 3.17/0.83  % (23258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.83  % (23258)Termination reason: Time limit
% 3.17/0.83  
% 3.17/0.83  % (23258)Memory used [KB]: 13560
% 3.17/0.83  % (23258)Time elapsed: 0.420 s
% 3.17/0.83  % (23258)------------------------------
% 3.17/0.83  % (23258)------------------------------
% 4.02/0.91  % (23266)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.02/0.92  % (23263)Time limit reached!
% 4.02/0.92  % (23263)------------------------------
% 4.02/0.92  % (23263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (23263)Termination reason: Time limit
% 4.02/0.92  
% 4.02/0.92  % (23263)Memory used [KB]: 4093
% 4.02/0.92  % (23263)Time elapsed: 0.520 s
% 4.02/0.92  % (23263)------------------------------
% 4.02/0.92  % (23263)------------------------------
% 4.29/0.94  % (23267)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.37/0.94  % (23240)Time limit reached!
% 4.37/0.94  % (23240)------------------------------
% 4.37/0.94  % (23240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.94  % (23240)Termination reason: Time limit
% 4.37/0.94  % (23240)Termination phase: Saturation
% 4.37/0.94  
% 4.37/0.94  % (23240)Memory used [KB]: 14839
% 4.37/0.94  % (23240)Time elapsed: 0.500 s
% 4.37/0.94  % (23240)------------------------------
% 4.37/0.94  % (23240)------------------------------
% 4.37/0.95  % (23268)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.37/0.95  % (23248)Time limit reached!
% 4.37/0.95  % (23248)------------------------------
% 4.37/0.95  % (23248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.95  % (23248)Termination reason: Time limit
% 4.37/0.95  
% 4.37/0.95  % (23248)Memory used [KB]: 5884
% 4.37/0.95  % (23248)Time elapsed: 0.506 s
% 4.37/0.95  % (23248)------------------------------
% 4.37/0.95  % (23248)------------------------------
% 4.37/0.96  % (23269)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.37/1.00  % (23241)Time limit reached!
% 4.37/1.00  % (23241)------------------------------
% 4.37/1.00  % (23241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/1.00  % (23241)Termination reason: Time limit
% 4.37/1.00  
% 4.37/1.00  % (23241)Memory used [KB]: 5884
% 4.37/1.00  % (23241)Time elapsed: 0.604 s
% 4.37/1.00  % (23241)------------------------------
% 4.37/1.00  % (23241)------------------------------
% 4.83/1.07  % (23270)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.83/1.07  % (23271)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.64/1.08  % (23272)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.33/1.17  % (23273)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.57/1.21  % (23235)Time limit reached!
% 6.57/1.21  % (23235)------------------------------
% 6.57/1.21  % (23235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.57/1.21  % (23235)Termination reason: Time limit
% 6.57/1.21  % (23235)Termination phase: Saturation
% 6.57/1.21  
% 6.57/1.21  % (23235)Memory used [KB]: 6524
% 6.57/1.21  % (23235)Time elapsed: 0.800 s
% 6.57/1.21  % (23235)------------------------------
% 6.57/1.21  % (23235)------------------------------
% 6.81/1.29  % (23256)Refutation found. Thanks to Tanya!
% 6.81/1.29  % SZS status Theorem for theBenchmark
% 6.81/1.29  % SZS output start Proof for theBenchmark
% 6.81/1.29  fof(f4108,plain,(
% 6.81/1.29    $false),
% 6.81/1.29    inference(unit_resulting_resolution,[],[f81,f3190,f142])).
% 6.81/1.29  fof(f142,plain,(
% 6.81/1.29    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f141])).
% 6.81/1.29  fof(f141,plain,(
% 6.81/1.29    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(equality_resolution,[],[f125])).
% 6.81/1.29  fof(f125,plain,(
% 6.81/1.29    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f70])).
% 6.81/1.29  fof(f70,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.81/1.29    inference(nnf_transformation,[],[f45])).
% 6.81/1.29  fof(f45,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.81/1.29    inference(flattening,[],[f44])).
% 6.81/1.29  fof(f44,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.81/1.29    inference(ennf_transformation,[],[f14])).
% 6.81/1.29  fof(f14,axiom,(
% 6.81/1.29    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 6.81/1.29  fof(f3190,plain,(
% 6.81/1.29    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 6.81/1.29    inference(backward_demodulation,[],[f3182,f3186])).
% 6.81/1.29  fof(f3186,plain,(
% 6.81/1.29    k1_xboole_0 = sK4),
% 6.81/1.29    inference(subsumption_resolution,[],[f3185,f81])).
% 6.81/1.29  fof(f3185,plain,(
% 6.81/1.29    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) | k1_xboole_0 = sK4),
% 6.81/1.29    inference(forward_demodulation,[],[f3184,f139])).
% 6.81/1.29  fof(f139,plain,(
% 6.81/1.29    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.81/1.29    inference(equality_resolution,[],[f102])).
% 6.81/1.29  fof(f102,plain,(
% 6.81/1.29    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 6.81/1.29    inference(cnf_transformation,[],[f62])).
% 6.81/1.29  fof(f62,plain,(
% 6.81/1.29    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.81/1.29    inference(flattening,[],[f61])).
% 6.81/1.29  fof(f61,plain,(
% 6.81/1.29    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.81/1.29    inference(nnf_transformation,[],[f2])).
% 6.81/1.29  fof(f2,axiom,(
% 6.81/1.29    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 6.81/1.29  fof(f3184,plain,(
% 6.81/1.29    ~m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK4)) | k1_xboole_0 = sK4),
% 6.81/1.29    inference(forward_demodulation,[],[f3183,f3046])).
% 6.81/1.29  fof(f3046,plain,(
% 6.81/1.29    k1_xboole_0 = sK2),
% 6.81/1.29    inference(forward_demodulation,[],[f2847,f147])).
% 6.81/1.29  fof(f147,plain,(
% 6.81/1.29    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.81/1.29    inference(superposition,[],[f134,f130])).
% 6.81/1.29  fof(f130,plain,(
% 6.81/1.29    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 6.81/1.29    inference(definition_unfolding,[],[f80,f82])).
% 6.81/1.29  fof(f82,plain,(
% 6.81/1.29    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.81/1.29    inference(cnf_transformation,[],[f18])).
% 6.81/1.29  fof(f18,axiom,(
% 6.81/1.29    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 6.81/1.29  fof(f80,plain,(
% 6.81/1.29    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 6.81/1.29    inference(cnf_transformation,[],[f7])).
% 6.81/1.29  fof(f7,axiom,(
% 6.81/1.29    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 6.81/1.29  fof(f134,plain,(
% 6.81/1.29    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 6.81/1.29    inference(definition_unfolding,[],[f87,f82])).
% 6.81/1.29  fof(f87,plain,(
% 6.81/1.29    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.81/1.29    inference(cnf_transformation,[],[f6])).
% 6.81/1.29  fof(f6,axiom,(
% 6.81/1.29    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 6.81/1.29  fof(f2847,plain,(
% 6.81/1.29    sK2 = k1_relat_1(k1_xboole_0)),
% 6.81/1.29    inference(backward_demodulation,[],[f246,f2840])).
% 6.81/1.29  fof(f2840,plain,(
% 6.81/1.29    k1_xboole_0 = sK3),
% 6.81/1.29    inference(subsumption_resolution,[],[f2829,f76])).
% 6.81/1.29  fof(f76,plain,(
% 6.81/1.29    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.81/1.29    inference(cnf_transformation,[],[f57])).
% 6.81/1.29  fof(f57,plain,(
% 6.81/1.29    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 6.81/1.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f56,f55])).
% 6.81/1.29  fof(f55,plain,(
% 6.81/1.29    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 6.81/1.29    introduced(choice_axiom,[])).
% 6.81/1.29  fof(f56,plain,(
% 6.81/1.29    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 6.81/1.29    introduced(choice_axiom,[])).
% 6.81/1.29  fof(f27,plain,(
% 6.81/1.29    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.81/1.29    inference(flattening,[],[f26])).
% 6.81/1.29  fof(f26,plain,(
% 6.81/1.29    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.81/1.29    inference(ennf_transformation,[],[f25])).
% 6.81/1.29  fof(f25,negated_conjecture,(
% 6.81/1.29    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.81/1.29    inference(negated_conjecture,[],[f24])).
% 6.81/1.29  fof(f24,conjecture,(
% 6.81/1.29    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 6.81/1.29  fof(f2829,plain,(
% 6.81/1.29    k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.81/1.29    inference(resolution,[],[f2314,f142])).
% 6.81/1.29  fof(f2314,plain,(
% 6.81/1.29    ~r2_relset_1(sK2,sK2,sK4,sK4) | k1_xboole_0 = sK3),
% 6.81/1.29    inference(superposition,[],[f79,f2206])).
% 6.81/1.29  fof(f2206,plain,(
% 6.81/1.29    k6_partfun1(sK2) = sK4 | k1_xboole_0 = sK3),
% 6.81/1.29    inference(forward_demodulation,[],[f2205,f139])).
% 6.81/1.29  fof(f2205,plain,(
% 6.81/1.29    sK3 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | k6_partfun1(sK2) = sK4),
% 6.81/1.29    inference(subsumption_resolution,[],[f2204,f81])).
% 6.81/1.29  fof(f2204,plain,(
% 6.81/1.29    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) | sK3 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | k6_partfun1(sK2) = sK4),
% 6.81/1.29    inference(forward_demodulation,[],[f2136,f139])).
% 6.81/1.29  fof(f2136,plain,(
% 6.81/1.29    ~m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK3)) | sK3 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | k6_partfun1(sK2) = sK4),
% 6.81/1.29    inference(superposition,[],[f167,f2128])).
% 6.81/1.29  fof(f2128,plain,(
% 6.81/1.29    k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4),
% 6.81/1.29    inference(subsumption_resolution,[],[f2127,f316])).
% 6.81/1.29  fof(f316,plain,(
% 6.81/1.29    r2_relset_1(sK2,sK2,sK3,sK3)),
% 6.81/1.29    inference(backward_demodulation,[],[f77,f313])).
% 6.81/1.29  fof(f313,plain,(
% 6.81/1.29    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.81/1.29    inference(subsumption_resolution,[],[f312,f74])).
% 6.81/1.29  fof(f74,plain,(
% 6.81/1.29    v1_funct_1(sK4)),
% 6.81/1.29    inference(cnf_transformation,[],[f57])).
% 6.81/1.29  fof(f312,plain,(
% 6.81/1.29    ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.81/1.29    inference(subsumption_resolution,[],[f311,f76])).
% 6.81/1.29  fof(f311,plain,(
% 6.81/1.29    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.81/1.29    inference(subsumption_resolution,[],[f310,f71])).
% 6.81/1.29  fof(f71,plain,(
% 6.81/1.29    v1_funct_1(sK3)),
% 6.81/1.29    inference(cnf_transformation,[],[f57])).
% 6.81/1.29  fof(f310,plain,(
% 6.81/1.29    ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.81/1.29    inference(subsumption_resolution,[],[f304,f73])).
% 6.81/1.29  fof(f73,plain,(
% 6.81/1.29    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.81/1.29    inference(cnf_transformation,[],[f57])).
% 6.81/1.29  fof(f304,plain,(
% 6.81/1.29    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.81/1.29    inference(resolution,[],[f128,f229])).
% 6.81/1.29  fof(f229,plain,(
% 6.81/1.29    ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.81/1.29    inference(subsumption_resolution,[],[f221,f73])).
% 6.81/1.29  fof(f221,plain,(
% 6.81/1.29    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.81/1.29    inference(resolution,[],[f124,f77])).
% 6.81/1.29  fof(f124,plain,(
% 6.81/1.29    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f70])).
% 6.81/1.29  fof(f128,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.81/1.29    inference(cnf_transformation,[],[f49])).
% 6.81/1.29  fof(f49,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.81/1.29    inference(flattening,[],[f48])).
% 6.81/1.29  fof(f48,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.81/1.29    inference(ennf_transformation,[],[f15])).
% 6.81/1.29  fof(f15,axiom,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 6.81/1.29  fof(f77,plain,(
% 6.81/1.29    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 6.81/1.29    inference(cnf_transformation,[],[f57])).
% 6.81/1.29  fof(f2127,plain,(
% 6.81/1.29    ~r2_relset_1(sK2,sK2,sK3,sK3) | k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4),
% 6.81/1.29    inference(forward_demodulation,[],[f2126,f1565])).
% 6.81/1.29  fof(f1565,plain,(
% 6.81/1.29    sK3 = k5_relat_1(k6_partfun1(sK2),sK3)),
% 6.81/1.29    inference(resolution,[],[f1555,f73])).
% 6.81/1.29  fof(f1555,plain,(
% 6.81/1.29    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | sK3 = k5_relat_1(k6_partfun1(sK2),sK3)) )),
% 6.81/1.29    inference(resolution,[],[f1535,f73])).
% 6.81/1.29  fof(f1535,plain,(
% 6.81/1.29    ( ! [X26,X25] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | sK3 = k5_relat_1(k6_partfun1(sK2),sK3)) )),
% 6.81/1.29    inference(resolution,[],[f1524,f71])).
% 6.81/1.29  fof(f1524,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | k5_relat_1(k6_partfun1(sK2),X0) = X0) )),
% 6.81/1.29    inference(resolution,[],[f1288,f86])).
% 6.81/1.29  fof(f86,plain,(
% 6.81/1.29    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f16])).
% 6.81/1.29  fof(f16,axiom,(
% 6.81/1.29    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 6.81/1.29  fof(f1288,plain,(
% 6.81/1.29    ( ! [X6,X8,X7,X9] : (~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X7))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X7))) | k5_relat_1(k6_partfun1(sK2),X6) = X6) )),
% 6.81/1.29    inference(resolution,[],[f1278,f466])).
% 6.81/1.29  fof(f466,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(k6_partfun1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_1(X1) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X4))) | k5_relat_1(k6_partfun1(X0),X1) = X1) )),
% 6.81/1.29    inference(resolution,[],[f338,f309])).
% 6.81/1.29  fof(f309,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f306])).
% 6.81/1.29  fof(f306,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.81/1.29    inference(superposition,[],[f128,f126])).
% 6.81/1.29  fof(f126,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.81/1.29    inference(cnf_transformation,[],[f47])).
% 6.81/1.29  fof(f47,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.81/1.29    inference(flattening,[],[f46])).
% 6.81/1.29  fof(f46,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.81/1.29    inference(ennf_transformation,[],[f17])).
% 6.81/1.29  fof(f17,axiom,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 6.81/1.29  fof(f338,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (~m1_subset_1(k5_relat_1(k6_partfun1(X1),X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k6_partfun1(X1),X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f335])).
% 6.81/1.29  fof(f335,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k6_partfun1(X1),X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(k5_relat_1(k6_partfun1(X1),X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 6.81/1.29    inference(resolution,[],[f265,f124])).
% 6.81/1.29  fof(f265,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f264,f86])).
% 6.81/1.29  fof(f264,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f259])).
% 6.81/1.29  fof(f259,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.81/1.29    inference(superposition,[],[f106,f129])).
% 6.81/1.29  fof(f129,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f51])).
% 6.81/1.29  fof(f51,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.81/1.29    inference(flattening,[],[f50])).
% 6.81/1.29  fof(f50,plain,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.81/1.29    inference(ennf_transformation,[],[f13])).
% 6.81/1.29  fof(f13,axiom,(
% 6.81/1.29    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 6.81/1.29  fof(f106,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f37])).
% 6.81/1.29  fof(f37,plain,(
% 6.81/1.29    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.81/1.29    inference(ennf_transformation,[],[f19])).
% 6.81/1.29  fof(f19,axiom,(
% 6.81/1.29    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).
% 6.81/1.29  fof(f1278,plain,(
% 6.81/1.29    v1_funct_1(k6_partfun1(sK2))),
% 6.81/1.29    inference(resolution,[],[f1270,f73])).
% 6.81/1.29  fof(f1270,plain,(
% 6.81/1.29    ( ! [X6,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.81/1.29    inference(resolution,[],[f1264,f73])).
% 6.81/1.29  fof(f1264,plain,(
% 6.81/1.29    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.81/1.29    inference(resolution,[],[f1262,f73])).
% 6.81/1.29  fof(f1262,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1261,f249])).
% 6.81/1.29  fof(f249,plain,(
% 6.81/1.29    ( ! [X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(backward_demodulation,[],[f203,f246])).
% 6.81/1.29  fof(f203,plain,(
% 6.81/1.29    ( ! [X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(resolution,[],[f174,f71])).
% 6.81/1.29  fof(f174,plain,(
% 6.81/1.29    ( ! [X2,X3,X1] : (~v1_funct_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 6.81/1.29    inference(resolution,[],[f91,f103])).
% 6.81/1.29  fof(f103,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f34])).
% 6.81/1.29  fof(f34,plain,(
% 6.81/1.29    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.81/1.29    inference(ennf_transformation,[],[f10])).
% 6.81/1.29  fof(f10,axiom,(
% 6.81/1.29    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 6.81/1.29  fof(f91,plain,(
% 6.81/1.29    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f29])).
% 6.81/1.29  fof(f29,plain,(
% 6.81/1.29    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.81/1.29    inference(flattening,[],[f28])).
% 6.81/1.29  fof(f28,plain,(
% 6.81/1.29    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.81/1.29    inference(ennf_transformation,[],[f22])).
% 6.81/1.29  fof(f22,axiom,(
% 6.81/1.29    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 6.81/1.29  fof(f1261,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(forward_demodulation,[],[f1260,f246])).
% 6.81/1.29  fof(f1260,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1259,f71])).
% 6.81/1.29  fof(f1259,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(trivial_inequality_removal,[],[f1255])).
% 6.81/1.29  fof(f1255,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(resolution,[],[f1218,f157])).
% 6.81/1.29  fof(f157,plain,(
% 6.81/1.29    ( ! [X2,X3,X1] : (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 6.81/1.29    inference(resolution,[],[f90,f103])).
% 6.81/1.29  fof(f90,plain,(
% 6.81/1.29    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f29])).
% 6.81/1.29  fof(f1218,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK3,X5,X4) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relat_1(sK3) != X4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1217,f71])).
% 6.81/1.29  fof(f1217,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relat_1(sK3) != X4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | ~v1_funct_2(sK3,X5,X4) | ~v1_funct_1(sK3)) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1212,f78])).
% 6.81/1.29  fof(f78,plain,(
% 6.81/1.29    v2_funct_1(sK3)),
% 6.81/1.29    inference(cnf_transformation,[],[f57])).
% 6.81/1.29  fof(f1212,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relat_1(sK3) != X4 | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | ~v1_funct_2(sK3,X5,X4) | ~v1_funct_1(sK3)) )),
% 6.81/1.29    inference(resolution,[],[f1209,f283])).
% 6.81/1.29  fof(f283,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relat_1(X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f282])).
% 6.81/1.29  fof(f282,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (k2_relat_1(X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(superposition,[],[f110,f105])).
% 6.81/1.29  fof(f105,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f36])).
% 6.81/1.29  fof(f36,plain,(
% 6.81/1.29    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.81/1.29    inference(ennf_transformation,[],[f12])).
% 6.81/1.29  fof(f12,axiom,(
% 6.81/1.29    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 6.81/1.29  fof(f110,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.81/1.29    inference(cnf_transformation,[],[f39])).
% 6.81/1.29  fof(f39,plain,(
% 6.81/1.29    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.81/1.29    inference(flattening,[],[f38])).
% 6.81/1.29  fof(f38,plain,(
% 6.81/1.29    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.81/1.29    inference(ennf_transformation,[],[f21])).
% 6.81/1.29  fof(f21,axiom,(
% 6.81/1.29    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 6.81/1.29  fof(f1209,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1208,f249])).
% 6.81/1.29  fof(f1208,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(forward_demodulation,[],[f1207,f246])).
% 6.81/1.29  fof(f1207,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1206,f71])).
% 6.81/1.29  fof(f1206,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(trivial_inequality_removal,[],[f1202])).
% 6.81/1.29  fof(f1202,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != k2_relat_1(sK3) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.81/1.29    inference(resolution,[],[f980,f157])).
% 6.81/1.29  fof(f980,plain,(
% 6.81/1.29    ( ! [X26,X24,X23,X27,X25,X22] : (~v1_funct_2(sK3,X27,X24) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.81/1.29    inference(forward_demodulation,[],[f979,f246])).
% 6.81/1.29  fof(f979,plain,(
% 6.81/1.29    ( ! [X26,X24,X23,X27,X25,X22] : (v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f973,f71])).
% 6.81/1.29  fof(f973,plain,(
% 6.81/1.29    ( ! [X26,X24,X23,X27,X25,X22] : (v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | ~v1_funct_1(sK3) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 6.81/1.29    inference(resolution,[],[f762,f78])).
% 6.81/1.29  fof(f762,plain,(
% 6.81/1.29    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X2) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | k2_relat_1(X2) != X1 | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f761])).
% 6.81/1.29  fof(f761,plain,(
% 6.81/1.29    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(X2) != X1 | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.81/1.29    inference(superposition,[],[f570,f105])).
% 6.81/1.29  fof(f570,plain,(
% 6.81/1.29    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relset_1(X5,X6,X0) != X6 | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f569])).
% 6.81/1.29  fof(f569,plain,(
% 6.81/1.29    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 6.81/1.29    inference(resolution,[],[f365,f108])).
% 6.81/1.29  fof(f108,plain,(
% 6.81/1.29    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.81/1.29    inference(cnf_transformation,[],[f39])).
% 6.81/1.29  fof(f365,plain,(
% 6.81/1.29    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5)) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f362,f103])).
% 6.81/1.29  fof(f362,plain,(
% 6.81/1.29    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_relat_1(X5)) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f360])).
% 6.81/1.29  fof(f360,plain,(
% 6.81/1.29    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 6.81/1.29    inference(superposition,[],[f289,f136])).
% 6.81/1.29  fof(f136,plain,(
% 6.81/1.29    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.81/1.29    inference(definition_unfolding,[],[f92,f82])).
% 6.81/1.29  fof(f92,plain,(
% 6.81/1.29    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.81/1.29    inference(cnf_transformation,[],[f31])).
% 6.81/1.29  fof(f31,plain,(
% 6.81/1.29    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.81/1.29    inference(flattening,[],[f30])).
% 6.81/1.29  fof(f30,plain,(
% 6.81/1.29    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.81/1.29    inference(ennf_transformation,[],[f9])).
% 6.81/1.29  fof(f9,axiom,(
% 6.81/1.29    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 6.81/1.29  fof(f289,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f288])).
% 6.81/1.29  fof(f288,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.81/1.29    inference(superposition,[],[f127,f126])).
% 6.81/1.29  fof(f127,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.81/1.29    inference(cnf_transformation,[],[f49])).
% 6.81/1.29  fof(f2126,plain,(
% 6.81/1.29    k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k6_partfun1(sK2) = sK4),
% 6.81/1.29    inference(subsumption_resolution,[],[f2125,f1278])).
% 6.81/1.29  fof(f2125,plain,(
% 6.81/1.29    k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k6_partfun1(sK2) = sK4),
% 6.81/1.29    inference(subsumption_resolution,[],[f2116,f86])).
% 6.81/1.29  fof(f2116,plain,(
% 6.81/1.29    k1_xboole_0 = sK2 | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k6_partfun1(sK2) = sK4),
% 6.81/1.29    inference(resolution,[],[f1979,f1285])).
% 6.81/1.29  fof(f1285,plain,(
% 6.81/1.29    v1_funct_2(k6_partfun1(sK2),sK2,sK2)),
% 6.81/1.29    inference(resolution,[],[f1278,f159])).
% 6.81/1.29  fof(f159,plain,(
% 6.81/1.29    ( ! [X0] : (~v1_funct_1(k6_partfun1(X0)) | v1_funct_2(k6_partfun1(X0),X0,X0)) )),
% 6.81/1.29    inference(forward_demodulation,[],[f158,f134])).
% 6.81/1.29  fof(f158,plain,(
% 6.81/1.29    ( ! [X0] : (v1_funct_2(k6_partfun1(X0),k1_relat_1(k6_partfun1(X0)),X0) | ~v1_funct_1(k6_partfun1(X0))) )),
% 6.81/1.29    inference(forward_demodulation,[],[f155,f133])).
% 6.81/1.29  fof(f133,plain,(
% 6.81/1.29    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 6.81/1.29    inference(definition_unfolding,[],[f88,f82])).
% 6.81/1.29  fof(f88,plain,(
% 6.81/1.29    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 6.81/1.29    inference(cnf_transformation,[],[f6])).
% 6.81/1.29  fof(f155,plain,(
% 6.81/1.29    ( ! [X0] : (~v1_funct_1(k6_partfun1(X0)) | v1_funct_2(k6_partfun1(X0),k1_relat_1(k6_partfun1(X0)),k2_relat_1(k6_partfun1(X0)))) )),
% 6.81/1.29    inference(resolution,[],[f90,f132])).
% 6.81/1.29  fof(f132,plain,(
% 6.81/1.29    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 6.81/1.29    inference(definition_unfolding,[],[f83,f82])).
% 6.81/1.29  fof(f83,plain,(
% 6.81/1.29    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 6.81/1.29    inference(cnf_transformation,[],[f8])).
% 6.81/1.29  fof(f8,axiom,(
% 6.81/1.29    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 6.81/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 6.81/1.29  fof(f1979,plain,(
% 6.81/1.29    ( ! [X0] : (~v1_funct_2(X0,sK2,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | ~v1_funct_1(X0) | sK4 = X0) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1978,f71])).
% 6.81/1.29  fof(f1978,plain,(
% 6.81/1.29    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~v1_funct_1(sK3)) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1963,f73])).
% 6.81/1.29  fof(f1963,plain,(
% 6.81/1.29    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3)) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f1962])).
% 6.81/1.29  fof(f1962,plain,(
% 6.81/1.29    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(X0)) )),
% 6.81/1.29    inference(superposition,[],[f1631,f126])).
% 6.81/1.29  fof(f1631,plain,(
% 6.81/1.29    ( ! [X8] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X8,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X8,sK2,sK2) | ~v1_funct_1(X8) | sK4 = X8) )),
% 6.81/1.29    inference(forward_demodulation,[],[f1630,f313])).
% 6.81/1.29  fof(f1630,plain,(
% 6.81/1.29    ( ! [X8] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X8,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | k1_xboole_0 = sK2 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X8,sK2,sK2) | ~v1_funct_1(X8) | sK4 = X8) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1629,f74])).
% 6.81/1.29  fof(f1629,plain,(
% 6.81/1.29    ( ! [X8] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X8,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X8,sK2,sK2) | ~v1_funct_1(X8) | sK4 = X8) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1617,f76])).
% 6.81/1.29  fof(f1617,plain,(
% 6.81/1.29    ( ! [X8] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X8,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X8,sK2,sK2) | ~v1_funct_1(X8) | sK4 = X8) )),
% 6.81/1.29    inference(resolution,[],[f1041,f75])).
% 6.81/1.29  fof(f75,plain,(
% 6.81/1.29    v1_funct_2(sK4,sK2,sK2)),
% 6.81/1.29    inference(cnf_transformation,[],[f57])).
% 6.81/1.29  fof(f1041,plain,(
% 6.81/1.29    ( ! [X6,X7,X5] : (~v1_funct_2(X7,X5,sK2) | ~r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | X6 = X7) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f1031,f73])).
% 6.81/1.29  fof(f1031,plain,(
% 6.81/1.29    ( ! [X6,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X7,X5,sK2) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | X6 = X7) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f1029])).
% 6.81/1.29  fof(f1029,plain,(
% 6.81/1.29    ( ! [X6,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X7,X5,sK2) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | k1_xboole_0 = sK2 | X6 = X7) )),
% 6.81/1.29    inference(resolution,[],[f869,f72])).
% 6.81/1.29  fof(f72,plain,(
% 6.81/1.29    v1_funct_2(sK3,sK2,sK2)),
% 6.81/1.29    inference(cnf_transformation,[],[f57])).
% 6.81/1.29  fof(f869,plain,(
% 6.81/1.29    ( ! [X23,X21,X19,X22,X20] : (~v1_funct_2(sK3,X19,X20) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | k1_xboole_0 = X20 | ~r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X23,X21,X19) | ~v1_funct_1(X23) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X22,X21,X19) | ~v1_funct_1(X22) | k1_xboole_0 = X19 | X22 = X23) )),
% 6.81/1.29    inference(subsumption_resolution,[],[f867,f71])).
% 6.81/1.29  fof(f867,plain,(
% 6.81/1.29    ( ! [X23,X21,X19,X22,X20] : (~v1_funct_2(sK3,X19,X20) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | k1_xboole_0 = X20 | ~r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X23,X21,X19) | ~v1_funct_1(X23) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X22,X21,X19) | ~v1_funct_1(X22) | k1_xboole_0 = X19 | X22 = X23) )),
% 6.81/1.29    inference(resolution,[],[f691,f78])).
% 6.81/1.29  fof(f691,plain,(
% 6.81/1.29    ( ! [X12,X10,X8,X7,X11,X9] : (~v2_funct_1(X7) | ~v1_funct_2(X7,X8,X9) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k1_xboole_0 = X9 | ~r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X12,X10,X8) | ~v1_funct_1(X12) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X11,X10,X8) | ~v1_funct_1(X11) | k1_xboole_0 = X8 | X11 = X12) )),
% 6.81/1.29    inference(duplicate_literal_removal,[],[f690])).
% 6.81/1.29  fof(f690,plain,(
% 6.81/1.29    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(X7,X8,X9) | ~v1_funct_1(X7) | ~v2_funct_1(X7) | k1_xboole_0 = X9 | ~r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X12,X10,X8) | ~v1_funct_1(X12) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X11,X10,X8) | ~v1_funct_1(X11) | k1_xboole_0 = X8 | X11 = X12 | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))) )),
% 6.81/1.29    inference(resolution,[],[f371,f124])).
% 6.81/1.29  fof(f371,plain,(
% 6.81/1.29    ( ! [X4,X2,X0,X5,X3,X1] : (r2_relset_1(X3,X0,X4,X5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X1,X0,X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | k1_xboole_0 = X2 | ~r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4) | k1_xboole_0 = X0) )),
% 6.81/1.29    inference(resolution,[],[f234,f113])).
% 6.81/1.29  fof(f113,plain,(
% 6.81/1.29    ( ! [X6,X2,X0,X8,X7,X1] : (~sP0(X0,X1,X2) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7) | r2_relset_1(X6,X0,X7,X8)) )),
% 6.81/1.29    inference(cnf_transformation,[],[f69])).
% 7.36/1.31  fof(f69,plain,(
% 7.36/1.31    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2)))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 7.36/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f66,f68,f67])).
% 7.36/1.31  fof(f67,plain,(
% 7.36/1.31    ! [X2,X1,X0] : (? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2))))),
% 7.36/1.31    introduced(choice_axiom,[])).
% 7.36/1.31  fof(f68,plain,(
% 7.36/1.31    ! [X2,X1,X0] : (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) => (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))))),
% 7.36/1.31    introduced(choice_axiom,[])).
% 7.36/1.31  fof(f66,plain,(
% 7.36/1.31    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 7.36/1.31    inference(rectify,[],[f65])).
% 7.36/1.31  fof(f65,plain,(
% 7.36/1.31    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)) | ~sP0(X0,X2,X1)))),
% 7.36/1.31    inference(nnf_transformation,[],[f52])).
% 7.36/1.31  fof(f52,plain,(
% 7.36/1.31    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))),
% 7.36/1.31    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.36/1.31  fof(f234,plain,(
% 7.36/1.31    ( ! [X2,X0,X1] : (sP0(X1,X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X0) )),
% 7.36/1.31    inference(resolution,[],[f122,f111])).
% 7.36/1.31  fof(f111,plain,(
% 7.36/1.31    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v2_funct_1(X1) | sP0(X2,X1,X0)) )),
% 7.36/1.31    inference(cnf_transformation,[],[f64])).
% 7.36/1.31  fof(f64,plain,(
% 7.36/1.31    ! [X0,X1,X2] : (((v2_funct_1(X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v2_funct_1(X1))) | ~sP1(X0,X1,X2))),
% 7.36/1.31    inference(rectify,[],[f63])).
% 7.36/1.31  fof(f63,plain,(
% 7.36/1.31    ! [X1,X2,X0] : (((v2_funct_1(X2) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~v2_funct_1(X2))) | ~sP1(X1,X2,X0))),
% 7.36/1.31    inference(nnf_transformation,[],[f53])).
% 7.36/1.31  fof(f53,plain,(
% 7.36/1.31    ! [X1,X2,X0] : ((v2_funct_1(X2) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 7.36/1.31    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.36/1.31  fof(f122,plain,(
% 7.36/1.31    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.36/1.31    inference(cnf_transformation,[],[f54])).
% 7.36/1.31  fof(f54,plain,(
% 7.36/1.31    ! [X0,X1,X2] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.36/1.31    inference(definition_folding,[],[f41,f53,f52])).
% 7.36/1.31  fof(f41,plain,(
% 7.36/1.31    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.36/1.31    inference(flattening,[],[f40])).
% 7.36/1.31  fof(f40,plain,(
% 7.36/1.31    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : ((r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.36/1.31    inference(ennf_transformation,[],[f20])).
% 7.36/1.31  fof(f20,axiom,(
% 7.36/1.31    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~(v2_funct_1(X2) <=> ! [X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) => (r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) => r2_relset_1(X3,X0,X4,X5))))) & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 7.36/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).
% 7.36/1.31  fof(f167,plain,(
% 7.36/1.31    ~m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK3)) | sK3 = k2_zfmisc_1(sK2,sK2)),
% 7.36/1.31    inference(resolution,[],[f164,f73])).
% 7.36/1.31  fof(f164,plain,(
% 7.36/1.31    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | X1 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 7.36/1.31    inference(resolution,[],[f154,f98])).
% 7.36/1.31  fof(f98,plain,(
% 7.36/1.31    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.36/1.31    inference(cnf_transformation,[],[f60])).
% 7.36/1.31  fof(f60,plain,(
% 7.36/1.31    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.36/1.31    inference(nnf_transformation,[],[f4])).
% 7.36/1.31  fof(f4,axiom,(
% 7.36/1.31    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.36/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 7.36/1.31  fof(f154,plain,(
% 7.36/1.31    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 7.36/1.31    inference(resolution,[],[f97,f98])).
% 7.36/1.31  fof(f97,plain,(
% 7.36/1.31    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 7.36/1.31    inference(cnf_transformation,[],[f59])).
% 7.36/1.31  fof(f59,plain,(
% 7.36/1.31    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.36/1.31    inference(flattening,[],[f58])).
% 7.36/1.31  fof(f58,plain,(
% 7.36/1.31    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.36/1.31    inference(nnf_transformation,[],[f1])).
% 7.36/1.31  fof(f1,axiom,(
% 7.36/1.31    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.36/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.36/1.31  fof(f79,plain,(
% 7.36/1.31    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 7.36/1.31    inference(cnf_transformation,[],[f57])).
% 7.36/1.31  fof(f246,plain,(
% 7.36/1.31    sK2 = k1_relat_1(sK3)),
% 7.36/1.31    inference(subsumption_resolution,[],[f245,f71])).
% 7.36/1.31  fof(f245,plain,(
% 7.36/1.31    sK2 = k1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 7.36/1.31    inference(subsumption_resolution,[],[f242,f73])).
% 7.36/1.31  fof(f242,plain,(
% 7.36/1.31    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 7.36/1.31    inference(resolution,[],[f211,f72])).
% 7.36/1.31  fof(f211,plain,(
% 7.36/1.31    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relat_1(X1) = X0 | ~v1_funct_1(X1)) )),
% 7.36/1.31    inference(duplicate_literal_removal,[],[f208])).
% 7.36/1.31  fof(f208,plain,(
% 7.36/1.31    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.36/1.31    inference(superposition,[],[f94,f104])).
% 7.36/1.31  fof(f104,plain,(
% 7.36/1.31    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.36/1.31    inference(cnf_transformation,[],[f35])).
% 7.36/1.31  fof(f35,plain,(
% 7.36/1.31    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.36/1.31    inference(ennf_transformation,[],[f11])).
% 7.36/1.31  fof(f11,axiom,(
% 7.36/1.31    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.36/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 7.36/1.31  fof(f94,plain,(
% 7.36/1.31    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.36/1.31    inference(cnf_transformation,[],[f33])).
% 7.36/1.31  fof(f33,plain,(
% 7.36/1.31    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.36/1.31    inference(flattening,[],[f32])).
% 7.36/1.31  fof(f32,plain,(
% 7.36/1.31    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.36/1.31    inference(ennf_transformation,[],[f23])).
% 7.36/1.31  fof(f23,axiom,(
% 7.36/1.31    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 7.36/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 7.36/1.31  fof(f3183,plain,(
% 7.36/1.31    k1_xboole_0 = sK4 | ~m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4))),
% 7.36/1.31    inference(forward_demodulation,[],[f3050,f139])).
% 7.36/1.31  fof(f3050,plain,(
% 7.36/1.31    sK4 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4))),
% 7.36/1.31    inference(backward_demodulation,[],[f168,f3046])).
% 7.36/1.31  fof(f168,plain,(
% 7.36/1.31    ~m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4)) | k2_zfmisc_1(sK2,sK2) = sK4),
% 7.36/1.31    inference(resolution,[],[f164,f76])).
% 7.36/1.31  fof(f3182,plain,(
% 7.36/1.31    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0)),
% 7.36/1.31    inference(forward_demodulation,[],[f3049,f130])).
% 7.36/1.31  fof(f3049,plain,(
% 7.36/1.31    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0))),
% 7.36/1.31    inference(backward_demodulation,[],[f79,f3046])).
% 7.36/1.31  fof(f81,plain,(
% 7.36/1.31    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.36/1.31    inference(cnf_transformation,[],[f3])).
% 7.36/1.31  fof(f3,axiom,(
% 7.36/1.31    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.36/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 7.36/1.31  % SZS output end Proof for theBenchmark
% 7.36/1.31  % (23256)------------------------------
% 7.36/1.31  % (23256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.36/1.31  % (23256)Termination reason: Refutation
% 7.36/1.31  
% 7.36/1.31  % (23256)Memory used [KB]: 9978
% 7.36/1.31  % (23256)Time elapsed: 0.841 s
% 7.36/1.31  % (23256)------------------------------
% 7.36/1.31  % (23256)------------------------------
% 7.36/1.31  % (23233)Success in time 0.951 s
%------------------------------------------------------------------------------
