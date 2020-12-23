%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1003+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:02 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.83s
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
fof(f5009,plain,(
    $false ),
    inference(global_subsumption,[],[f5006,f5008])).

fof(f5008,plain,(
    k1_xboole_0 != sK158 ),
    inference(subsumption_resolution,[],[f5007,f4817])).

fof(f4817,plain,(
    ! [X1] : ~ sP73(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f3739])).

fof(f3739,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP73(X0,X1) ) ),
    inference(cnf_transformation,[],[f2870])).

fof(f2870,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP73(X0,X1) ) ),
    inference(nnf_transformation,[],[f2436])).

fof(f2436,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP73(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP73])])).

fof(f5007,plain,
    ( sP73(k1_xboole_0,sK158)
    | k1_xboole_0 != sK158 ),
    inference(superposition,[],[f5004,f3240])).

fof(f3240,plain,
    ( k1_xboole_0 = sK157
    | k1_xboole_0 != sK158 ),
    inference(cnf_transformation,[],[f2566])).

fof(f2566,plain,
    ( sK157 != k8_relset_1(sK157,sK158,sK159,k7_relset_1(sK157,sK158,sK159,sK157))
    & ( k1_xboole_0 = sK157
      | k1_xboole_0 != sK158 )
    & m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK157,sK158)))
    & v1_funct_2(sK159,sK157,sK158)
    & v1_funct_1(sK159) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK157,sK158,sK159])],[f1551,f2565])).

fof(f2565,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK157 != k8_relset_1(sK157,sK158,sK159,k7_relset_1(sK157,sK158,sK159,sK157))
      & ( k1_xboole_0 = sK157
        | k1_xboole_0 != sK158 )
      & m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK157,sK158)))
      & v1_funct_2(sK159,sK157,sK158)
      & v1_funct_1(sK159) ) ),
    introduced(choice_axiom,[])).

fof(f1551,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1550])).

fof(f1550,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1533])).

fof(f1533,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1532])).

fof(f1532,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

fof(f5004,plain,(
    sP73(sK157,sK158) ),
    inference(subsumption_resolution,[],[f5003,f4897])).

fof(f4897,plain,(
    sP74(sK157,sK159,sK158) ),
    inference(resolution,[],[f3239,f3740])).

fof(f3740,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP74(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f2439])).

fof(f2439,plain,(
    ! [X0,X1,X2] :
      ( ( sP75(X2,X1,X0)
        & sP74(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f1823,f2438,f2437,f2436])).

fof(f2437,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP73(X0,X1)
      | ~ sP74(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP74])])).

fof(f2438,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP75(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP75])])).

fof(f1823,plain,(
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
    inference(flattening,[],[f1822])).

fof(f1822,plain,(
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

fof(f3239,plain,(
    m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK157,sK158))) ),
    inference(cnf_transformation,[],[f2566])).

fof(f5003,plain,
    ( sP73(sK157,sK158)
    | ~ sP74(sK157,sK159,sK158) ),
    inference(subsumption_resolution,[],[f5001,f3238])).

fof(f3238,plain,(
    v1_funct_2(sK159,sK157,sK158) ),
    inference(cnf_transformation,[],[f2566])).

fof(f5001,plain,
    ( ~ v1_funct_2(sK159,sK157,sK158)
    | sP73(sK157,sK158)
    | ~ sP74(sK157,sK159,sK158) ),
    inference(trivial_inequality_removal,[],[f4998])).

fof(f4998,plain,
    ( sK157 != sK157
    | ~ v1_funct_2(sK159,sK157,sK158)
    | sP73(sK157,sK158)
    | ~ sP74(sK157,sK159,sK158) ),
    inference(superposition,[],[f4956,f3736])).

fof(f3736,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP73(X0,X2)
      | ~ sP74(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2869])).

fof(f2869,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP73(X0,X2)
      | ~ sP74(X0,X1,X2) ) ),
    inference(rectify,[],[f2868])).

fof(f2868,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP73(X0,X1)
      | ~ sP74(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f2437])).

fof(f4956,plain,(
    sK157 != k1_relset_1(sK157,sK158,sK159) ),
    inference(subsumption_resolution,[],[f4949,f3239])).

fof(f4949,plain,
    ( sK157 != k1_relset_1(sK157,sK158,sK159)
    | ~ m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK157,sK158))) ),
    inference(superposition,[],[f3241,f3262])).

fof(f3262,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f1564])).

fof(f1564,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f1259])).

fof(f1259,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f3241,plain,(
    sK157 != k8_relset_1(sK157,sK158,sK159,k7_relset_1(sK157,sK158,sK159,sK157)) ),
    inference(cnf_transformation,[],[f2566])).

fof(f5006,plain,(
    k1_xboole_0 = sK158 ),
    inference(resolution,[],[f5004,f3738])).

fof(f3738,plain,(
    ! [X0,X1] :
      ( ~ sP73(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f2870])).
%------------------------------------------------------------------------------
