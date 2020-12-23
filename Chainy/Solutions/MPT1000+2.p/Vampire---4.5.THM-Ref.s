%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1000+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:02 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 118 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 582 expanded)
%              Number of equality atoms :   68 ( 282 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5095,plain,(
    $false ),
    inference(global_subsumption,[],[f5092,f5094])).

fof(f5094,plain,(
    k1_xboole_0 != sK158 ),
    inference(subsumption_resolution,[],[f5093,f4901])).

fof(f4901,plain,(
    ! [X1] : ~ sP59(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f3678])).

fof(f3678,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP59(X0,X1) ) ),
    inference(cnf_transformation,[],[f2833])).

fof(f2833,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP59(X0,X1) ) ),
    inference(nnf_transformation,[],[f2424])).

fof(f2424,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP59(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP59])])).

fof(f5093,plain,
    ( sP59(k1_xboole_0,sK158)
    | k1_xboole_0 != sK158 ),
    inference(superposition,[],[f5090,f3263])).

fof(f3263,plain,
    ( k1_xboole_0 = sK157
    | k1_xboole_0 != sK158 ),
    inference(cnf_transformation,[],[f2577])).

fof(f2577,plain,
    ( sK157 != k8_relset_1(sK157,sK158,sK159,sK158)
    & ( k1_xboole_0 = sK157
      | k1_xboole_0 != sK158 )
    & m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK157,sK158)))
    & v1_funct_2(sK159,sK157,sK158)
    & v1_funct_1(sK159) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK157,sK158,sK159])],[f1548,f2576])).

fof(f2576,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,X1) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK157 != k8_relset_1(sK157,sK158,sK159,sK158)
      & ( k1_xboole_0 = sK157
        | k1_xboole_0 != sK158 )
      & m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK157,sK158)))
      & v1_funct_2(sK159,sK157,sK158)
      & v1_funct_1(sK159) ) ),
    introduced(choice_axiom,[])).

fof(f1548,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1547])).

fof(f1547,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1529])).

fof(f1529,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f1528])).

fof(f1528,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f5090,plain,(
    sP59(sK157,sK158) ),
    inference(subsumption_resolution,[],[f5089,f4984])).

fof(f4984,plain,(
    sP60(sK157,sK159,sK158) ),
    inference(resolution,[],[f3262,f3679])).

fof(f3679,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP60(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f2427])).

fof(f2427,plain,(
    ! [X0,X1,X2] :
      ( ( sP61(X2,X1,X0)
        & sP60(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f1775,f2426,f2425,f2424])).

fof(f2425,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP59(X0,X1)
      | ~ sP60(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP60])])).

fof(f2426,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP61(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP61])])).

fof(f1775,plain,(
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
    inference(flattening,[],[f1774])).

fof(f1774,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f3262,plain,(
    m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK157,sK158))) ),
    inference(cnf_transformation,[],[f2577])).

fof(f5089,plain,
    ( sP59(sK157,sK158)
    | ~ sP60(sK157,sK159,sK158) ),
    inference(subsumption_resolution,[],[f5087,f3261])).

fof(f3261,plain,(
    v1_funct_2(sK159,sK157,sK158) ),
    inference(cnf_transformation,[],[f2577])).

fof(f5087,plain,
    ( ~ v1_funct_2(sK159,sK157,sK158)
    | sP59(sK157,sK158)
    | ~ sP60(sK157,sK159,sK158) ),
    inference(trivial_inequality_removal,[],[f5084])).

fof(f5084,plain,
    ( sK157 != sK157
    | ~ v1_funct_2(sK159,sK157,sK158)
    | sP59(sK157,sK158)
    | ~ sP60(sK157,sK159,sK158) ),
    inference(superposition,[],[f5046,f3675])).

fof(f3675,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP59(X0,X2)
      | ~ sP60(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2832])).

fof(f2832,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP59(X0,X2)
      | ~ sP60(X0,X1,X2) ) ),
    inference(rectify,[],[f2831])).

fof(f2831,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP59(X0,X1)
      | ~ sP60(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f2425])).

fof(f5046,plain,(
    sK157 != k1_relset_1(sK157,sK158,sK159) ),
    inference(subsumption_resolution,[],[f5044,f3262])).

fof(f5044,plain,
    ( sK157 != k1_relset_1(sK157,sK158,sK159)
    | ~ m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK157,sK158))) ),
    inference(superposition,[],[f3264,f3277])).

fof(f3277,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1556])).

fof(f1556,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1258])).

fof(f1258,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f3264,plain,(
    sK157 != k8_relset_1(sK157,sK158,sK159,sK158) ),
    inference(cnf_transformation,[],[f2577])).

fof(f5092,plain,(
    k1_xboole_0 = sK158 ),
    inference(resolution,[],[f5090,f3677])).

fof(f3677,plain,(
    ! [X0,X1] :
      ( ~ sP59(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f2833])).
%------------------------------------------------------------------------------
