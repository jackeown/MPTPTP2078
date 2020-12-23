%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:49 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  290 (1297 expanded)
%              Number of leaves         :   40 ( 411 expanded)
%              Depth                    :   27
%              Number of atoms          : 1238 (11706 expanded)
%              Number of equality atoms :  302 (3954 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f272,f278,f372,f437,f621,f654,f669,f714,f728,f929,f1170,f1201,f1247,f1302,f1375])).

fof(f1375,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(avatar_contradiction_clause,[],[f1374])).

fof(f1374,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1349,f293])).

fof(f293,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f112,f271])).

fof(f271,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl4_2
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f112,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f94,f93])).

fof(f93,plain,
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

fof(f94,plain,
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
    inference(ennf_transformation,[],[f40])).

fof(f40,negated_conjecture,(
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
    inference(negated_conjecture,[],[f39])).

fof(f39,conjecture,(
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

fof(f1349,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(backward_demodulation,[],[f381,f1341])).

fof(f1341,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1340,f465])).

fof(f465,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f283,f461])).

fof(f461,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f460,f181])).

fof(f181,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f160,f147])).

fof(f147,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f160,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f460,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f459,f317])).

fof(f317,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f255,f271])).

fof(f255,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f254,f101])).

fof(f101,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

fof(f254,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f253,f102])).

fof(f102,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f95])).

fof(f253,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f252,f103])).

fof(f103,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f95])).

fof(f252,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f251,f109])).

fof(f109,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

fof(f251,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f234,f111])).

fof(f111,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f95])).

fof(f234,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f233])).

fof(f233,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f114,f107])).

fof(f107,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f95])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f459,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k4_relat_1(sK2),sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f458,f271])).

fof(f458,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f206,f266])).

fof(f266,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f206,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f197,f101])).

fof(f197,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f109,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f283,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f266,f163])).

fof(f163,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f1340,plain,
    ( sK1 != k1_relat_1(k4_relat_1(sK2))
    | sK2 = k4_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f1339,f386])).

fof(f386,plain,
    ( sK1 = k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f380,f306])).

fof(f306,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f224,f218])).

fof(f218,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(global_subsumption,[],[f106,f217])).

fof(f217,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f216,f110])).

fof(f110,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f95])).

fof(f216,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f105,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
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
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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

fof(f105,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f95])).

fof(f106,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f95])).

fof(f224,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f106,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f380,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_3 ),
    inference(resolution,[],[f363,f164])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f363,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1339,plain,
    ( sK2 = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f1338,f727])).

fof(f727,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl4_21
  <=> sK2 = k2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1338,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27 ),
    inference(trivial_inequality_removal,[],[f1337])).

fof(f1337,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f1336,f290])).

fof(f290,plain,
    ( sK0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f284,f274])).

fof(f274,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f219,f215])).

fof(f215,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f103,f214])).

fof(f214,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f213,f111])).

fof(f213,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f102,f134])).

fof(f219,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f103,f167])).

fof(f284,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f266,f164])).

fof(f1336,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1335,f428])).

fof(f428,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl4_5
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1335,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1334,f299])).

fof(f299,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f298,f266])).

fof(f298,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f295,f101])).

fof(f295,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f129,f271])).

fof(f129,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1334,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1333,f612])).

fof(f612,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f611])).

fof(f611,plain,
    ( spl4_11
  <=> v1_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1333,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1332,f918])).

fof(f918,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f917])).

fof(f917,plain,
    ( spl4_27
  <=> v1_funct_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1332,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f1326,f722])).

fof(f722,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f721])).

fof(f721,plain,
    ( spl4_20
  <=> v2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1326,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(superposition,[],[f174,f1250])).

fof(f1250,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f1235,f182])).

fof(f182,plain,(
    ! [X0] : k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f162,f147,f147])).

fof(f162,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f1235,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f892,f1222])).

fof(f1222,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f527,f653])).

fof(f653,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f651])).

fof(f651,plain,
    ( spl4_15
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f527,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f523,f104])).

fof(f104,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f95])).

fof(f523,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f222,f106])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f220,f101])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f103,f150])).

fof(f150,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f892,plain,
    ( k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f280,f363])).

fof(f280,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(sK2,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f266,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f174,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f120,f147])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f381,plain,
    ( sK3 = k4_relat_1(k4_relat_1(sK3))
    | ~ spl4_3 ),
    inference(resolution,[],[f363,f165])).

fof(f165,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f1302,plain,
    ( ~ spl4_3
    | ~ spl4_19
    | spl4_27 ),
    inference(avatar_contradiction_clause,[],[f1301])).

fof(f1301,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_19
    | spl4_27 ),
    inference(subsumption_resolution,[],[f1300,f363])).

fof(f1300,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_19
    | spl4_27 ),
    inference(subsumption_resolution,[],[f1299,f104])).

fof(f1299,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_19
    | spl4_27 ),
    inference(subsumption_resolution,[],[f1296,f919])).

fof(f919,plain,
    ( ~ v1_funct_1(k4_relat_1(sK3))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f917])).

fof(f1296,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(superposition,[],[f129,f1289])).

fof(f1289,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1288,f363])).

fof(f1288,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1268,f104])).

fof(f1268,plain,
    ( k4_relat_1(sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(resolution,[],[f713,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f713,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f711])).

fof(f711,plain,
    ( spl4_19
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1247,plain,
    ( ~ spl4_15
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f1246])).

fof(f1246,plain,
    ( $false
    | ~ spl4_15
    | spl4_18 ),
    inference(subsumption_resolution,[],[f1226,f176])).

fof(f176,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f142,f147])).

fof(f142,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1226,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ spl4_15
    | spl4_18 ),
    inference(backward_demodulation,[],[f751,f1222])).

fof(f751,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_18 ),
    inference(backward_demodulation,[],[f709,f527])).

fof(f709,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f707])).

fof(f707,plain,
    ( spl4_18
  <=> v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1201,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_14
    | ~ spl4_35 ),
    inference(avatar_contradiction_clause,[],[f1200])).

fof(f1200,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f1199,f101])).

fof(f1199,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f1198,f103])).

fof(f1198,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f1197,f299])).

fof(f1197,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f1196,f1162])).

fof(f1162,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1161,plain,
    ( spl4_35
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f1196,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f1191,f649])).

fof(f649,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl4_14
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1191,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_35 ),
    inference(superposition,[],[f149,f1182])).

fof(f1182,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f1181,f311])).

fof(f311,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f250,f271])).

fof(f250,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f249,f101])).

fof(f249,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f248,f102])).

fof(f248,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f247,f103])).

fof(f247,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f246,f109])).

fof(f246,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f235,f111])).

fof(f235,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f113,f107])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1181,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f1174,f299])).

fof(f1174,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_35 ),
    inference(resolution,[],[f1162,f222])).

fof(f149,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1170,plain,
    ( ~ spl4_2
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f1169])).

fof(f1169,plain,
    ( $false
    | ~ spl4_2
    | spl4_35 ),
    inference(subsumption_resolution,[],[f1155,f1163])).

fof(f1163,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1155,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1154,f103])).

fof(f1154,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1153,f107])).

fof(f1153,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f303,f102])).

fof(f303,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK2,X3,X2)
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f302,f101])).

fof(f302,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK2,X3,X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f297,f109])).

fof(f297,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ v2_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK2,X3,X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_2 ),
    inference(superposition,[],[f117,f271])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f929,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f928])).

fof(f928,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(trivial_inequality_removal,[],[f927])).

fof(f927,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(forward_demodulation,[],[f926,f461])).

fof(f926,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(subsumption_resolution,[],[f925,f428])).

fof(f925,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_20 ),
    inference(subsumption_resolution,[],[f340,f723])).

fof(f723,plain,
    ( ~ v2_funct_1(k4_relat_1(sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f721])).

fof(f340,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f339,f283])).

fof(f339,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k1_relat_1(k4_relat_1(sK2)))
    | v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f338,f299])).

fof(f338,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k1_relat_1(k4_relat_1(sK2)))
    | v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f337,f266])).

fof(f337,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k1_relat_1(k4_relat_1(sK2)))
    | v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f335,f101])).

fof(f335,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k1_relat_1(k4_relat_1(sK2)))
    | v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(superposition,[],[f175,f317])).

fof(f175,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f140,f147])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f728,plain,
    ( ~ spl4_20
    | spl4_21
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f719,f427,f269,f265,f725,f721])).

fof(f719,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f334,f428])).

fof(f334,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f333])).

fof(f333,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f332,f290])).

fof(f332,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f331,f299])).

fof(f331,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f330,f266])).

fof(f330,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f329,f101])).

fof(f329,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f328,f283])).

fof(f328,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(superposition,[],[f174,f311])).

fof(f714,plain,
    ( ~ spl4_18
    | spl4_19 ),
    inference(avatar_split_clause,[],[f609,f711,f707])).

fof(f609,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f608,f104])).

fof(f608,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f607,f110])).

fof(f607,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f603,f106])).

fof(f603,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f241,f105])).

fof(f241,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,sK1,X2)
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f240,f101])).

fof(f240,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f239,f102])).

fof(f239,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f237,f103])).

fof(f237,plain,(
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
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,(
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
    inference(superposition,[],[f132,f107])).

fof(f132,plain,(
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
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f669,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f668])).

fof(f668,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f667,f101])).

fof(f667,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f666,f103])).

fof(f666,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f665,f104])).

fof(f665,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f664,f106])).

fof(f664,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_13 ),
    inference(resolution,[],[f645,f149])).

fof(f645,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f643])).

fof(f643,plain,
    ( spl4_13
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f654,plain,
    ( ~ spl4_13
    | ~ spl4_14
    | spl4_15 ),
    inference(avatar_split_clause,[],[f260,f651,f647,f643])).

fof(f260,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f108,f143])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f108,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f95])).

fof(f621,plain,
    ( ~ spl4_3
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | ~ spl4_3
    | spl4_11 ),
    inference(subsumption_resolution,[],[f618,f363])).

fof(f618,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_11 ),
    inference(resolution,[],[f613,f166])).

fof(f166,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f613,plain,
    ( ~ v1_relat_1(k4_relat_1(sK3))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f611])).

fof(f437,plain,
    ( ~ spl4_1
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f434,f266])).

fof(f434,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_5 ),
    inference(resolution,[],[f429,f166])).

fof(f429,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f427])).

fof(f372,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f370,f152])).

fof(f152,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f370,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_3 ),
    inference(resolution,[],[f369,f106])).

fof(f369,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_3 ),
    inference(resolution,[],[f364,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f364,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f362])).

fof(f278,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f276,f152])).

fof(f276,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f273,f103])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f267,f151])).

fof(f267,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f265])).

fof(f272,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f212,f269,f265])).

fof(f212,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f203,f101])).

fof(f203,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f109,f127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (19181)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.49  % (19197)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.50  % (19189)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.50  % (19196)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (19177)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (19200)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (19184)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (19188)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (19182)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (19186)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (19185)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (19187)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (19199)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (19204)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (19192)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (19191)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (19198)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (19183)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (19205)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (19195)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (19193)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (19190)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (19194)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (19179)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (19206)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (19178)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (19180)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.55  % (19202)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (19201)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (19203)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (19193)Refutation not found, incomplete strategy% (19193)------------------------------
% 0.20/0.56  % (19193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (19193)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (19193)Memory used [KB]: 10746
% 0.20/0.56  % (19193)Time elapsed: 0.153 s
% 0.20/0.56  % (19193)------------------------------
% 0.20/0.56  % (19193)------------------------------
% 1.87/0.61  % (19201)Refutation found. Thanks to Tanya!
% 1.87/0.61  % SZS status Theorem for theBenchmark
% 1.87/0.61  % SZS output start Proof for theBenchmark
% 1.87/0.61  fof(f1380,plain,(
% 1.87/0.61    $false),
% 1.87/0.61    inference(avatar_sat_refutation,[],[f272,f278,f372,f437,f621,f654,f669,f714,f728,f929,f1170,f1201,f1247,f1302,f1375])).
% 1.87/0.61  fof(f1375,plain,(
% 1.87/0.61    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_21 | ~spl4_27),
% 1.87/0.61    inference(avatar_contradiction_clause,[],[f1374])).
% 1.87/0.61  fof(f1374,plain,(
% 1.87/0.61    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_21 | ~spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1349,f293])).
% 1.87/0.61  fof(f293,plain,(
% 1.87/0.61    sK3 != k4_relat_1(sK2) | ~spl4_2),
% 1.87/0.61    inference(superposition,[],[f112,f271])).
% 1.87/0.61  fof(f271,plain,(
% 1.87/0.61    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl4_2),
% 1.87/0.61    inference(avatar_component_clause,[],[f269])).
% 1.87/0.61  fof(f269,plain,(
% 1.87/0.61    spl4_2 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.87/0.61  fof(f112,plain,(
% 1.87/0.61    k2_funct_1(sK2) != sK3),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f95,plain,(
% 1.87/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f94,f93])).
% 1.87/0.61  fof(f93,plain,(
% 1.87/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f94,plain,(
% 1.87/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f43,plain,(
% 1.87/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.87/0.61    inference(flattening,[],[f42])).
% 1.87/0.61  fof(f42,plain,(
% 1.87/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.87/0.61    inference(ennf_transformation,[],[f40])).
% 1.87/0.61  fof(f40,negated_conjecture,(
% 1.87/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.87/0.61    inference(negated_conjecture,[],[f39])).
% 1.87/0.61  fof(f39,conjecture,(
% 1.87/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.87/0.61  fof(f1349,plain,(
% 1.87/0.61    sK3 = k4_relat_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_21 | ~spl4_27)),
% 1.87/0.61    inference(backward_demodulation,[],[f381,f1341])).
% 1.87/0.61  fof(f1341,plain,(
% 1.87/0.61    sK2 = k4_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_21 | ~spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1340,f465])).
% 1.87/0.61  fof(f465,plain,(
% 1.87/0.61    sK1 = k1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.61    inference(backward_demodulation,[],[f283,f461])).
% 1.87/0.61  fof(f461,plain,(
% 1.87/0.61    sK1 = k2_relat_1(sK2) | (~spl4_1 | ~spl4_2)),
% 1.87/0.61    inference(forward_demodulation,[],[f460,f181])).
% 1.87/0.61  fof(f181,plain,(
% 1.87/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.87/0.61    inference(definition_unfolding,[],[f160,f147])).
% 1.87/0.61  fof(f147,plain,(
% 1.87/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f34])).
% 1.87/0.61  fof(f34,axiom,(
% 1.87/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.87/0.61  fof(f160,plain,(
% 1.87/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f12])).
% 1.87/0.61  fof(f12,axiom,(
% 1.87/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.87/0.61  fof(f460,plain,(
% 1.87/0.61    k2_relat_1(sK2) = k1_relat_1(k6_partfun1(sK1)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.61    inference(forward_demodulation,[],[f459,f317])).
% 1.87/0.61  fof(f317,plain,(
% 1.87/0.61    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2) | ~spl4_2),
% 1.87/0.61    inference(forward_demodulation,[],[f255,f271])).
% 1.87/0.61  fof(f255,plain,(
% 1.87/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.87/0.61    inference(subsumption_resolution,[],[f254,f101])).
% 1.87/0.61  fof(f101,plain,(
% 1.87/0.61    v1_funct_1(sK2)),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f254,plain,(
% 1.87/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_1(sK2)),
% 1.87/0.61    inference(subsumption_resolution,[],[f253,f102])).
% 1.87/0.61  fof(f102,plain,(
% 1.87/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f253,plain,(
% 1.87/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.61    inference(subsumption_resolution,[],[f252,f103])).
% 1.87/0.61  fof(f103,plain,(
% 1.87/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f252,plain,(
% 1.87/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.61    inference(subsumption_resolution,[],[f251,f109])).
% 1.87/0.61  fof(f109,plain,(
% 1.87/0.61    v2_funct_1(sK2)),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f251,plain,(
% 1.87/0.61    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.61    inference(subsumption_resolution,[],[f234,f111])).
% 1.87/0.61  fof(f111,plain,(
% 1.87/0.61    k1_xboole_0 != sK1),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f234,plain,(
% 1.87/0.61    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.61    inference(trivial_inequality_removal,[],[f233])).
% 1.87/0.61  fof(f233,plain,(
% 1.87/0.61    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.61    inference(superposition,[],[f114,f107])).
% 1.87/0.61  fof(f107,plain,(
% 1.87/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f114,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f45])).
% 1.87/0.61  fof(f45,plain,(
% 1.87/0.61    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.87/0.61    inference(flattening,[],[f44])).
% 1.87/0.61  fof(f44,plain,(
% 1.87/0.61    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.87/0.61    inference(ennf_transformation,[],[f38])).
% 1.87/0.61  fof(f38,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.87/0.61  fof(f459,plain,(
% 1.87/0.61    k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k4_relat_1(sK2),sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.61    inference(forward_demodulation,[],[f458,f271])).
% 1.87/0.61  fof(f458,plain,(
% 1.87/0.61    k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~spl4_1),
% 1.87/0.61    inference(subsumption_resolution,[],[f206,f266])).
% 1.87/0.61  fof(f266,plain,(
% 1.87/0.61    v1_relat_1(sK2) | ~spl4_1),
% 1.87/0.61    inference(avatar_component_clause,[],[f265])).
% 1.87/0.61  fof(f265,plain,(
% 1.87/0.61    spl4_1 <=> v1_relat_1(sK2)),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.87/0.61  fof(f206,plain,(
% 1.87/0.61    k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2)),
% 1.87/0.61    inference(subsumption_resolution,[],[f197,f101])).
% 1.87/0.61  fof(f197,plain,(
% 1.87/0.61    k2_relat_1(sK2) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.87/0.61    inference(resolution,[],[f109,f121])).
% 1.87/0.61  fof(f121,plain,(
% 1.87/0.61    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f55])).
% 1.87/0.61  fof(f55,plain,(
% 1.87/0.61    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(flattening,[],[f54])).
% 1.87/0.61  fof(f54,plain,(
% 1.87/0.61    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f24])).
% 1.87/0.61  fof(f24,axiom,(
% 1.87/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 1.87/0.61  fof(f283,plain,(
% 1.87/0.61    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | ~spl4_1),
% 1.87/0.61    inference(resolution,[],[f266,f163])).
% 1.87/0.61  fof(f163,plain,(
% 1.87/0.61    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f86])).
% 1.87/0.61  fof(f86,plain,(
% 1.87/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f10])).
% 1.87/0.61  fof(f10,axiom,(
% 1.87/0.61    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.87/0.61  fof(f1340,plain,(
% 1.87/0.61    sK1 != k1_relat_1(k4_relat_1(sK2)) | sK2 = k4_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_21 | ~spl4_27)),
% 1.87/0.61    inference(forward_demodulation,[],[f1339,f386])).
% 1.87/0.61  fof(f386,plain,(
% 1.87/0.61    sK1 = k2_relat_1(k4_relat_1(sK3)) | ~spl4_3),
% 1.87/0.61    inference(forward_demodulation,[],[f380,f306])).
% 1.87/0.61  fof(f306,plain,(
% 1.87/0.61    sK1 = k1_relat_1(sK3)),
% 1.87/0.61    inference(forward_demodulation,[],[f224,f218])).
% 1.87/0.61  fof(f218,plain,(
% 1.87/0.61    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.87/0.61    inference(global_subsumption,[],[f106,f217])).
% 1.87/0.61  fof(f217,plain,(
% 1.87/0.61    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.87/0.61    inference(subsumption_resolution,[],[f216,f110])).
% 1.87/0.61  fof(f110,plain,(
% 1.87/0.61    k1_xboole_0 != sK0),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f216,plain,(
% 1.87/0.61    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.87/0.61    inference(resolution,[],[f105,f134])).
% 1.87/0.61  fof(f134,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f96])).
% 1.87/0.61  fof(f96,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.61    inference(nnf_transformation,[],[f67])).
% 1.87/0.61  fof(f67,plain,(
% 1.87/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.61    inference(flattening,[],[f66])).
% 1.87/0.61  fof(f66,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.61    inference(ennf_transformation,[],[f29])).
% 1.87/0.61  fof(f29,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.87/0.61  fof(f105,plain,(
% 1.87/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f106,plain,(
% 1.87/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f224,plain,(
% 1.87/0.61    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 1.87/0.61    inference(resolution,[],[f106,f167])).
% 1.87/0.61  fof(f167,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f89])).
% 1.87/0.61  fof(f89,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.61    inference(ennf_transformation,[],[f27])).
% 1.87/0.61  fof(f27,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.87/0.61  fof(f380,plain,(
% 1.87/0.61    k1_relat_1(sK3) = k2_relat_1(k4_relat_1(sK3)) | ~spl4_3),
% 1.87/0.61    inference(resolution,[],[f363,f164])).
% 1.87/0.61  fof(f164,plain,(
% 1.87/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f86])).
% 1.87/0.61  fof(f363,plain,(
% 1.87/0.61    v1_relat_1(sK3) | ~spl4_3),
% 1.87/0.61    inference(avatar_component_clause,[],[f362])).
% 1.87/0.61  fof(f362,plain,(
% 1.87/0.61    spl4_3 <=> v1_relat_1(sK3)),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.87/0.61  fof(f1339,plain,(
% 1.87/0.61    sK2 = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_21 | ~spl4_27)),
% 1.87/0.61    inference(forward_demodulation,[],[f1338,f727])).
% 1.87/0.61  fof(f727,plain,(
% 1.87/0.61    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~spl4_21),
% 1.87/0.61    inference(avatar_component_clause,[],[f725])).
% 1.87/0.61  fof(f725,plain,(
% 1.87/0.61    spl4_21 <=> sK2 = k2_funct_1(k4_relat_1(sK2))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.87/0.61  fof(f1338,plain,(
% 1.87/0.61    k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27)),
% 1.87/0.61    inference(trivial_inequality_removal,[],[f1337])).
% 1.87/0.61  fof(f1337,plain,(
% 1.87/0.61    k6_partfun1(sK0) != k6_partfun1(sK0) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27)),
% 1.87/0.61    inference(forward_demodulation,[],[f1336,f290])).
% 1.87/0.61  fof(f290,plain,(
% 1.87/0.61    sK0 = k2_relat_1(k4_relat_1(sK2)) | ~spl4_1),
% 1.87/0.61    inference(forward_demodulation,[],[f284,f274])).
% 1.87/0.61  fof(f274,plain,(
% 1.87/0.61    sK0 = k1_relat_1(sK2)),
% 1.87/0.61    inference(forward_demodulation,[],[f219,f215])).
% 1.87/0.61  fof(f215,plain,(
% 1.87/0.61    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.87/0.61    inference(global_subsumption,[],[f103,f214])).
% 1.87/0.61  fof(f214,plain,(
% 1.87/0.61    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.87/0.61    inference(subsumption_resolution,[],[f213,f111])).
% 1.87/0.61  fof(f213,plain,(
% 1.87/0.61    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.87/0.61    inference(resolution,[],[f102,f134])).
% 1.87/0.61  fof(f219,plain,(
% 1.87/0.61    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.87/0.61    inference(resolution,[],[f103,f167])).
% 1.87/0.61  fof(f284,plain,(
% 1.87/0.61    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl4_1),
% 1.87/0.61    inference(resolution,[],[f266,f164])).
% 1.87/0.61  fof(f1336,plain,(
% 1.87/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1335,f428])).
% 1.87/0.61  fof(f428,plain,(
% 1.87/0.61    v1_relat_1(k4_relat_1(sK2)) | ~spl4_5),
% 1.87/0.61    inference(avatar_component_clause,[],[f427])).
% 1.87/0.61  fof(f427,plain,(
% 1.87/0.61    spl4_5 <=> v1_relat_1(k4_relat_1(sK2))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.87/0.61  fof(f1335,plain,(
% 1.87/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1334,f299])).
% 1.87/0.61  fof(f299,plain,(
% 1.87/0.61    v1_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.61    inference(subsumption_resolution,[],[f298,f266])).
% 1.87/0.61  fof(f298,plain,(
% 1.87/0.61    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_2),
% 1.87/0.61    inference(subsumption_resolution,[],[f295,f101])).
% 1.87/0.61  fof(f295,plain,(
% 1.87/0.61    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 1.87/0.61    inference(superposition,[],[f129,f271])).
% 1.87/0.61  fof(f129,plain,(
% 1.87/0.61    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f63])).
% 1.87/0.61  fof(f63,plain,(
% 1.87/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(flattening,[],[f62])).
% 1.87/0.61  fof(f62,plain,(
% 1.87/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f17])).
% 1.87/0.61  fof(f17,axiom,(
% 1.87/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.87/0.61  fof(f1334,plain,(
% 1.87/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1333,f612])).
% 1.87/0.61  fof(f612,plain,(
% 1.87/0.61    v1_relat_1(k4_relat_1(sK3)) | ~spl4_11),
% 1.87/0.61    inference(avatar_component_clause,[],[f611])).
% 1.87/0.61  fof(f611,plain,(
% 1.87/0.61    spl4_11 <=> v1_relat_1(k4_relat_1(sK3))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.87/0.61  fof(f1333,plain,(
% 1.87/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_15 | ~spl4_20 | ~spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1332,f918])).
% 1.87/0.61  fof(f918,plain,(
% 1.87/0.61    v1_funct_1(k4_relat_1(sK3)) | ~spl4_27),
% 1.87/0.61    inference(avatar_component_clause,[],[f917])).
% 1.87/0.61  fof(f917,plain,(
% 1.87/0.61    spl4_27 <=> v1_funct_1(k4_relat_1(sK3))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.87/0.61  fof(f1332,plain,(
% 1.87/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_15 | ~spl4_20)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1326,f722])).
% 1.87/0.61  fof(f722,plain,(
% 1.87/0.61    v2_funct_1(k4_relat_1(sK2)) | ~spl4_20),
% 1.87/0.61    inference(avatar_component_clause,[],[f721])).
% 1.87/0.61  fof(f721,plain,(
% 1.87/0.61    spl4_20 <=> v2_funct_1(k4_relat_1(sK2))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.87/0.61  fof(f1326,plain,(
% 1.87/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 1.87/0.61    inference(superposition,[],[f174,f1250])).
% 1.87/0.61  fof(f1250,plain,(
% 1.87/0.61    k6_partfun1(sK0) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 1.87/0.61    inference(forward_demodulation,[],[f1235,f182])).
% 1.87/0.61  fof(f182,plain,(
% 1.87/0.61    ( ! [X0] : (k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0))) )),
% 1.87/0.61    inference(definition_unfolding,[],[f162,f147,f147])).
% 1.87/0.61  fof(f162,plain,(
% 1.87/0.61    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f13])).
% 1.87/0.61  fof(f13,axiom,(
% 1.87/0.61    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 1.87/0.61  fof(f1235,plain,(
% 1.87/0.61    k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 1.87/0.61    inference(backward_demodulation,[],[f892,f1222])).
% 1.87/0.61  fof(f1222,plain,(
% 1.87/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_15),
% 1.87/0.61    inference(backward_demodulation,[],[f527,f653])).
% 1.87/0.61  fof(f653,plain,(
% 1.87/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_15),
% 1.87/0.61    inference(avatar_component_clause,[],[f651])).
% 1.87/0.61  fof(f651,plain,(
% 1.87/0.61    spl4_15 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.87/0.61  fof(f527,plain,(
% 1.87/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.87/0.61    inference(subsumption_resolution,[],[f523,f104])).
% 1.87/0.61  fof(f104,plain,(
% 1.87/0.61    v1_funct_1(sK3)),
% 1.87/0.61    inference(cnf_transformation,[],[f95])).
% 1.87/0.61  fof(f523,plain,(
% 1.87/0.61    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.87/0.61    inference(resolution,[],[f222,f106])).
% 1.87/0.61  fof(f222,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f220,f101])).
% 1.87/0.61  fof(f220,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 1.87/0.61    inference(resolution,[],[f103,f150])).
% 1.87/0.61  fof(f150,plain,(
% 1.87/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f77])).
% 1.87/0.61  fof(f77,plain,(
% 1.87/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.87/0.61    inference(flattening,[],[f76])).
% 1.87/0.61  fof(f76,plain,(
% 1.87/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.87/0.61    inference(ennf_transformation,[],[f33])).
% 1.87/0.61  fof(f33,axiom,(
% 1.87/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.87/0.61  fof(f892,plain,(
% 1.87/0.61    k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3)),
% 1.87/0.61    inference(resolution,[],[f280,f363])).
% 1.87/0.61  fof(f280,plain,(
% 1.87/0.61    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(sK2,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(sK2))) ) | ~spl4_1),
% 1.87/0.61    inference(resolution,[],[f266,f153])).
% 1.87/0.61  fof(f153,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f79])).
% 1.87/0.61  fof(f79,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f11])).
% 1.87/0.61  fof(f11,axiom,(
% 1.87/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.87/0.61  fof(f174,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(definition_unfolding,[],[f120,f147])).
% 1.87/0.61  fof(f120,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f53])).
% 1.87/0.61  fof(f53,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(flattening,[],[f52])).
% 1.87/0.61  fof(f52,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f25])).
% 1.87/0.61  fof(f25,axiom,(
% 1.87/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.87/0.61  fof(f381,plain,(
% 1.87/0.61    sK3 = k4_relat_1(k4_relat_1(sK3)) | ~spl4_3),
% 1.87/0.61    inference(resolution,[],[f363,f165])).
% 1.87/0.61  fof(f165,plain,(
% 1.87/0.61    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f87])).
% 1.87/0.61  fof(f87,plain,(
% 1.87/0.61    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f5])).
% 1.87/0.61  fof(f5,axiom,(
% 1.87/0.61    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.87/0.61  fof(f1302,plain,(
% 1.87/0.61    ~spl4_3 | ~spl4_19 | spl4_27),
% 1.87/0.61    inference(avatar_contradiction_clause,[],[f1301])).
% 1.87/0.61  fof(f1301,plain,(
% 1.87/0.61    $false | (~spl4_3 | ~spl4_19 | spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1300,f363])).
% 1.87/0.61  fof(f1300,plain,(
% 1.87/0.61    ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_19 | spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1299,f104])).
% 1.87/0.61  fof(f1299,plain,(
% 1.87/0.61    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_19 | spl4_27)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1296,f919])).
% 1.87/0.61  fof(f919,plain,(
% 1.87/0.61    ~v1_funct_1(k4_relat_1(sK3)) | spl4_27),
% 1.87/0.61    inference(avatar_component_clause,[],[f917])).
% 1.87/0.61  fof(f1296,plain,(
% 1.87/0.61    v1_funct_1(k4_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_19)),
% 1.87/0.61    inference(superposition,[],[f129,f1289])).
% 1.87/0.61  fof(f1289,plain,(
% 1.87/0.61    k4_relat_1(sK3) = k2_funct_1(sK3) | (~spl4_3 | ~spl4_19)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1288,f363])).
% 1.87/0.61  fof(f1288,plain,(
% 1.87/0.61    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_19),
% 1.87/0.61    inference(subsumption_resolution,[],[f1268,f104])).
% 1.87/0.61  fof(f1268,plain,(
% 1.87/0.61    k4_relat_1(sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_19),
% 1.87/0.61    inference(resolution,[],[f713,f127])).
% 1.87/0.61  fof(f127,plain,(
% 1.87/0.61    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f61])).
% 1.87/0.61  fof(f61,plain,(
% 1.87/0.61    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(flattening,[],[f60])).
% 1.87/0.61  fof(f60,plain,(
% 1.87/0.61    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f16])).
% 1.87/0.61  fof(f16,axiom,(
% 1.87/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.87/0.61  fof(f713,plain,(
% 1.87/0.61    v2_funct_1(sK3) | ~spl4_19),
% 1.87/0.61    inference(avatar_component_clause,[],[f711])).
% 1.87/0.61  fof(f711,plain,(
% 1.87/0.61    spl4_19 <=> v2_funct_1(sK3)),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.87/0.61  fof(f1247,plain,(
% 1.87/0.61    ~spl4_15 | spl4_18),
% 1.87/0.61    inference(avatar_contradiction_clause,[],[f1246])).
% 1.87/0.61  fof(f1246,plain,(
% 1.87/0.61    $false | (~spl4_15 | spl4_18)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1226,f176])).
% 1.87/0.61  fof(f176,plain,(
% 1.87/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.87/0.61    inference(definition_unfolding,[],[f142,f147])).
% 1.87/0.61  fof(f142,plain,(
% 1.87/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f18])).
% 1.87/0.61  fof(f18,axiom,(
% 1.87/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.87/0.61  fof(f1226,plain,(
% 1.87/0.61    ~v2_funct_1(k6_partfun1(sK0)) | (~spl4_15 | spl4_18)),
% 1.87/0.61    inference(backward_demodulation,[],[f751,f1222])).
% 1.87/0.61  fof(f751,plain,(
% 1.87/0.61    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_18),
% 1.87/0.61    inference(backward_demodulation,[],[f709,f527])).
% 1.87/0.61  fof(f709,plain,(
% 1.87/0.61    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl4_18),
% 1.87/0.61    inference(avatar_component_clause,[],[f707])).
% 1.87/0.61  fof(f707,plain,(
% 1.87/0.61    spl4_18 <=> v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.87/0.61  fof(f1201,plain,(
% 1.87/0.61    ~spl4_1 | ~spl4_2 | spl4_14 | ~spl4_35),
% 1.87/0.61    inference(avatar_contradiction_clause,[],[f1200])).
% 1.87/0.61  fof(f1200,plain,(
% 1.87/0.61    $false | (~spl4_1 | ~spl4_2 | spl4_14 | ~spl4_35)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1199,f101])).
% 1.87/0.61  fof(f1199,plain,(
% 1.87/0.61    ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_14 | ~spl4_35)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1198,f103])).
% 1.87/0.61  fof(f1198,plain,(
% 1.87/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_14 | ~spl4_35)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1197,f299])).
% 1.87/0.61  fof(f1197,plain,(
% 1.87/0.61    ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_14 | ~spl4_35)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1196,f1162])).
% 1.87/0.61  fof(f1162,plain,(
% 1.87/0.61    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_35),
% 1.87/0.61    inference(avatar_component_clause,[],[f1161])).
% 1.87/0.61  fof(f1161,plain,(
% 1.87/0.61    spl4_35 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.87/0.61  fof(f1196,plain,(
% 1.87/0.61    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_14 | ~spl4_35)),
% 1.87/0.61    inference(subsumption_resolution,[],[f1191,f649])).
% 1.87/0.61  fof(f649,plain,(
% 1.87/0.61    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_14),
% 1.87/0.61    inference(avatar_component_clause,[],[f647])).
% 1.87/0.61  fof(f647,plain,(
% 1.87/0.61    spl4_14 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.87/0.61  fof(f1191,plain,(
% 1.87/0.61    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_35)),
% 1.87/0.61    inference(superposition,[],[f149,f1182])).
% 1.87/0.62  fof(f1182,plain,(
% 1.87/0.62    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_35)),
% 1.87/0.62    inference(forward_demodulation,[],[f1181,f311])).
% 1.87/0.62  fof(f311,plain,(
% 1.87/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | ~spl4_2),
% 1.87/0.62    inference(forward_demodulation,[],[f250,f271])).
% 1.87/0.62  fof(f250,plain,(
% 1.87/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.87/0.62    inference(subsumption_resolution,[],[f249,f101])).
% 1.87/0.62  fof(f249,plain,(
% 1.87/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f248,f102])).
% 1.87/0.62  fof(f248,plain,(
% 1.87/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f247,f103])).
% 1.87/0.62  fof(f247,plain,(
% 1.87/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f246,f109])).
% 1.87/0.62  fof(f246,plain,(
% 1.87/0.62    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f235,f111])).
% 1.87/0.62  fof(f235,plain,(
% 1.87/0.62    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(trivial_inequality_removal,[],[f232])).
% 1.87/0.62  fof(f232,plain,(
% 1.87/0.62    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(superposition,[],[f113,f107])).
% 1.87/0.62  fof(f113,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f45])).
% 1.87/0.62  fof(f1181,plain,(
% 1.87/0.62    k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_35)),
% 1.87/0.62    inference(subsumption_resolution,[],[f1174,f299])).
% 1.87/0.62  fof(f1174,plain,(
% 1.87/0.62    ~v1_funct_1(k4_relat_1(sK2)) | k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | ~spl4_35),
% 1.87/0.62    inference(resolution,[],[f1162,f222])).
% 1.87/0.62  fof(f149,plain,(
% 1.87/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f75])).
% 1.87/0.62  fof(f75,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.87/0.62    inference(flattening,[],[f74])).
% 1.87/0.62  fof(f74,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.87/0.62    inference(ennf_transformation,[],[f31])).
% 1.87/0.62  fof(f31,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.87/0.62  fof(f1170,plain,(
% 1.87/0.62    ~spl4_2 | spl4_35),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f1169])).
% 1.87/0.62  fof(f1169,plain,(
% 1.87/0.62    $false | (~spl4_2 | spl4_35)),
% 1.87/0.62    inference(subsumption_resolution,[],[f1155,f1163])).
% 1.87/0.62  fof(f1163,plain,(
% 1.87/0.62    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_35),
% 1.87/0.62    inference(avatar_component_clause,[],[f1161])).
% 1.87/0.62  fof(f1155,plain,(
% 1.87/0.62    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 1.87/0.62    inference(subsumption_resolution,[],[f1154,f103])).
% 1.87/0.62  fof(f1154,plain,(
% 1.87/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 1.87/0.62    inference(subsumption_resolution,[],[f1153,f107])).
% 1.87/0.62  fof(f1153,plain,(
% 1.87/0.62    sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 1.87/0.62    inference(resolution,[],[f303,f102])).
% 1.87/0.62  fof(f303,plain,(
% 1.87/0.62    ( ! [X2,X3] : (~v1_funct_2(sK2,X3,X2) | k2_relset_1(X3,X2,sK2) != X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl4_2),
% 1.87/0.62    inference(subsumption_resolution,[],[f302,f101])).
% 1.87/0.62  fof(f302,plain,(
% 1.87/0.62    ( ! [X2,X3] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X3,X2,sK2) != X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK2,X3,X2) | ~v1_funct_1(sK2)) ) | ~spl4_2),
% 1.87/0.62    inference(subsumption_resolution,[],[f297,f109])).
% 1.87/0.62  fof(f297,plain,(
% 1.87/0.62    ( ! [X2,X3] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X3,X2,sK2) != X2 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK2,X3,X2) | ~v1_funct_1(sK2)) ) | ~spl4_2),
% 1.87/0.62    inference(superposition,[],[f117,f271])).
% 1.87/0.62  fof(f117,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f47])).
% 1.87/0.62  fof(f47,plain,(
% 1.87/0.62    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.87/0.62    inference(flattening,[],[f46])).
% 1.87/0.62  fof(f46,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.87/0.62    inference(ennf_transformation,[],[f37])).
% 1.87/0.62  fof(f37,axiom,(
% 1.87/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.87/0.62  fof(f929,plain,(
% 1.87/0.62    ~spl4_1 | ~spl4_2 | ~spl4_5 | spl4_20),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f928])).
% 1.87/0.62  fof(f928,plain,(
% 1.87/0.62    $false | (~spl4_1 | ~spl4_2 | ~spl4_5 | spl4_20)),
% 1.87/0.62    inference(trivial_inequality_removal,[],[f927])).
% 1.87/0.62  fof(f927,plain,(
% 1.87/0.62    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_5 | spl4_20)),
% 1.87/0.62    inference(forward_demodulation,[],[f926,f461])).
% 1.87/0.62  fof(f926,plain,(
% 1.87/0.62    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_5 | spl4_20)),
% 1.87/0.62    inference(subsumption_resolution,[],[f925,f428])).
% 1.87/0.62  fof(f925,plain,(
% 1.87/0.62    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | spl4_20)),
% 1.87/0.62    inference(subsumption_resolution,[],[f340,f723])).
% 1.87/0.62  fof(f723,plain,(
% 1.87/0.62    ~v2_funct_1(k4_relat_1(sK2)) | spl4_20),
% 1.87/0.62    inference(avatar_component_clause,[],[f721])).
% 1.87/0.62  fof(f340,plain,(
% 1.87/0.62    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(forward_demodulation,[],[f339,f283])).
% 1.87/0.62  fof(f339,plain,(
% 1.87/0.62    k6_partfun1(sK1) != k6_partfun1(k1_relat_1(k4_relat_1(sK2))) | v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f338,f299])).
% 1.87/0.62  fof(f338,plain,(
% 1.87/0.62    k6_partfun1(sK1) != k6_partfun1(k1_relat_1(k4_relat_1(sK2))) | v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f337,f266])).
% 1.87/0.62  fof(f337,plain,(
% 1.87/0.62    k6_partfun1(sK1) != k6_partfun1(k1_relat_1(k4_relat_1(sK2))) | v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_2),
% 1.87/0.62    inference(subsumption_resolution,[],[f335,f101])).
% 1.87/0.62  fof(f335,plain,(
% 1.87/0.62    k6_partfun1(sK1) != k6_partfun1(k1_relat_1(k4_relat_1(sK2))) | v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_2),
% 1.87/0.62    inference(superposition,[],[f175,f317])).
% 1.87/0.62  fof(f175,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(definition_unfolding,[],[f140,f147])).
% 1.87/0.62  fof(f140,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f69])).
% 1.87/0.62  fof(f69,plain,(
% 1.87/0.62    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(flattening,[],[f68])).
% 1.87/0.62  fof(f68,plain,(
% 1.87/0.62    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f21])).
% 1.87/0.62  fof(f21,axiom,(
% 1.87/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 1.87/0.62  fof(f728,plain,(
% 1.87/0.62    ~spl4_20 | spl4_21 | ~spl4_1 | ~spl4_2 | ~spl4_5),
% 1.87/0.62    inference(avatar_split_clause,[],[f719,f427,f269,f265,f725,f721])).
% 1.87/0.62  fof(f719,plain,(
% 1.87/0.62    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_5)),
% 1.87/0.62    inference(subsumption_resolution,[],[f334,f428])).
% 1.87/0.62  fof(f334,plain,(
% 1.87/0.62    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(trivial_inequality_removal,[],[f333])).
% 1.87/0.62  fof(f333,plain,(
% 1.87/0.62    k6_partfun1(sK0) != k6_partfun1(sK0) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(forward_demodulation,[],[f332,f290])).
% 1.87/0.62  fof(f332,plain,(
% 1.87/0.62    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f331,f299])).
% 1.87/0.62  fof(f331,plain,(
% 1.87/0.62    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f330,f266])).
% 1.87/0.62  fof(f330,plain,(
% 1.87/0.62    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f329,f101])).
% 1.87/0.62  fof(f329,plain,(
% 1.87/0.62    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f328,f283])).
% 1.87/0.62  fof(f328,plain,(
% 1.87/0.62    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_2),
% 1.87/0.62    inference(superposition,[],[f174,f311])).
% 1.87/0.62  fof(f714,plain,(
% 1.87/0.62    ~spl4_18 | spl4_19),
% 1.87/0.62    inference(avatar_split_clause,[],[f609,f711,f707])).
% 1.87/0.62  fof(f609,plain,(
% 1.87/0.62    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))),
% 1.87/0.62    inference(subsumption_resolution,[],[f608,f104])).
% 1.87/0.62  fof(f608,plain,(
% 1.87/0.62    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~v1_funct_1(sK3)),
% 1.87/0.62    inference(subsumption_resolution,[],[f607,f110])).
% 1.87/0.62  fof(f607,plain,(
% 1.87/0.62    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 1.87/0.62    inference(subsumption_resolution,[],[f603,f106])).
% 1.87/0.62  fof(f603,plain,(
% 1.87/0.62    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 1.87/0.62    inference(resolution,[],[f241,f105])).
% 1.87/0.62  fof(f241,plain,(
% 1.87/0.62    ( ! [X2,X3] : (~v1_funct_2(X3,sK1,X2) | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f240,f101])).
% 1.87/0.62  fof(f240,plain,(
% 1.87/0.62    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_1(sK2)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f239,f102])).
% 1.87/0.62  fof(f239,plain,(
% 1.87/0.62    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f237,f103])).
% 1.87/0.62  fof(f237,plain,(
% 1.87/0.62    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.87/0.62    inference(trivial_inequality_removal,[],[f230])).
% 1.87/0.62  fof(f230,plain,(
% 1.87/0.62    ( ! [X2,X3] : (sK1 != sK1 | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.87/0.62    inference(superposition,[],[f132,f107])).
% 1.87/0.62  fof(f132,plain,(
% 1.87/0.62    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f65])).
% 1.87/0.62  fof(f65,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.87/0.62    inference(flattening,[],[f64])).
% 1.87/0.62  fof(f64,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.87/0.62    inference(ennf_transformation,[],[f36])).
% 1.87/0.62  fof(f36,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.87/0.62  fof(f669,plain,(
% 1.87/0.62    spl4_13),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f668])).
% 1.87/0.62  fof(f668,plain,(
% 1.87/0.62    $false | spl4_13),
% 1.87/0.62    inference(subsumption_resolution,[],[f667,f101])).
% 1.87/0.62  fof(f667,plain,(
% 1.87/0.62    ~v1_funct_1(sK2) | spl4_13),
% 1.87/0.62    inference(subsumption_resolution,[],[f666,f103])).
% 1.87/0.62  fof(f666,plain,(
% 1.87/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_13),
% 1.87/0.62    inference(subsumption_resolution,[],[f665,f104])).
% 1.87/0.62  fof(f665,plain,(
% 1.87/0.62    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_13),
% 1.87/0.62    inference(subsumption_resolution,[],[f664,f106])).
% 1.87/0.62  fof(f664,plain,(
% 1.87/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_13),
% 1.87/0.62    inference(resolution,[],[f645,f149])).
% 1.87/0.62  fof(f645,plain,(
% 1.87/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_13),
% 1.87/0.62    inference(avatar_component_clause,[],[f643])).
% 1.87/0.62  fof(f643,plain,(
% 1.87/0.62    spl4_13 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.87/0.62  fof(f654,plain,(
% 1.87/0.62    ~spl4_13 | ~spl4_14 | spl4_15),
% 1.87/0.62    inference(avatar_split_clause,[],[f260,f651,f647,f643])).
% 1.87/0.62  fof(f260,plain,(
% 1.87/0.62    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.87/0.62    inference(resolution,[],[f108,f143])).
% 1.87/0.62  fof(f143,plain,(
% 1.87/0.62    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f97])).
% 1.87/0.62  fof(f97,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(nnf_transformation,[],[f71])).
% 1.87/0.62  fof(f71,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(flattening,[],[f70])).
% 1.87/0.62  fof(f70,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.87/0.62    inference(ennf_transformation,[],[f28])).
% 1.87/0.62  fof(f28,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.87/0.62  fof(f108,plain,(
% 1.87/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.87/0.62    inference(cnf_transformation,[],[f95])).
% 1.87/0.62  fof(f621,plain,(
% 1.87/0.62    ~spl4_3 | spl4_11),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f620])).
% 1.87/0.62  fof(f620,plain,(
% 1.87/0.62    $false | (~spl4_3 | spl4_11)),
% 1.87/0.62    inference(subsumption_resolution,[],[f618,f363])).
% 1.87/0.62  fof(f618,plain,(
% 1.87/0.62    ~v1_relat_1(sK3) | spl4_11),
% 1.87/0.62    inference(resolution,[],[f613,f166])).
% 1.87/0.62  fof(f166,plain,(
% 1.87/0.62    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f88])).
% 1.87/0.62  fof(f88,plain,(
% 1.87/0.62    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f3])).
% 1.87/0.62  fof(f3,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.87/0.62  fof(f613,plain,(
% 1.87/0.62    ~v1_relat_1(k4_relat_1(sK3)) | spl4_11),
% 1.87/0.62    inference(avatar_component_clause,[],[f611])).
% 1.87/0.62  fof(f437,plain,(
% 1.87/0.62    ~spl4_1 | spl4_5),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f436])).
% 1.87/0.62  fof(f436,plain,(
% 1.87/0.62    $false | (~spl4_1 | spl4_5)),
% 1.87/0.62    inference(subsumption_resolution,[],[f434,f266])).
% 1.87/0.62  fof(f434,plain,(
% 1.87/0.62    ~v1_relat_1(sK2) | spl4_5),
% 1.87/0.62    inference(resolution,[],[f429,f166])).
% 1.87/0.62  fof(f429,plain,(
% 1.87/0.62    ~v1_relat_1(k4_relat_1(sK2)) | spl4_5),
% 1.87/0.62    inference(avatar_component_clause,[],[f427])).
% 1.87/0.62  fof(f372,plain,(
% 1.87/0.62    spl4_3),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f371])).
% 1.87/0.62  fof(f371,plain,(
% 1.87/0.62    $false | spl4_3),
% 1.87/0.62    inference(subsumption_resolution,[],[f370,f152])).
% 1.87/0.62  fof(f152,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f4])).
% 1.87/0.62  fof(f4,axiom,(
% 1.87/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.87/0.62  fof(f370,plain,(
% 1.87/0.62    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_3),
% 1.87/0.62    inference(resolution,[],[f369,f106])).
% 1.87/0.62  fof(f369,plain,(
% 1.87/0.62    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_3),
% 1.87/0.62    inference(resolution,[],[f364,f151])).
% 1.87/0.62  fof(f151,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f78])).
% 1.87/0.62  fof(f78,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f2])).
% 1.87/0.62  fof(f2,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.87/0.62  fof(f364,plain,(
% 1.87/0.62    ~v1_relat_1(sK3) | spl4_3),
% 1.87/0.62    inference(avatar_component_clause,[],[f362])).
% 1.87/0.62  fof(f278,plain,(
% 1.87/0.62    spl4_1),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f277])).
% 1.87/0.62  fof(f277,plain,(
% 1.87/0.62    $false | spl4_1),
% 1.87/0.62    inference(subsumption_resolution,[],[f276,f152])).
% 1.87/0.62  fof(f276,plain,(
% 1.87/0.62    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 1.87/0.62    inference(resolution,[],[f273,f103])).
% 1.87/0.62  fof(f273,plain,(
% 1.87/0.62    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 1.87/0.62    inference(resolution,[],[f267,f151])).
% 1.87/0.62  fof(f267,plain,(
% 1.87/0.62    ~v1_relat_1(sK2) | spl4_1),
% 1.87/0.62    inference(avatar_component_clause,[],[f265])).
% 1.87/0.62  fof(f272,plain,(
% 1.87/0.62    ~spl4_1 | spl4_2),
% 1.87/0.62    inference(avatar_split_clause,[],[f212,f269,f265])).
% 1.87/0.62  fof(f212,plain,(
% 1.87/0.62    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f203,f101])).
% 1.87/0.62  fof(f203,plain,(
% 1.87/0.62    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.87/0.62    inference(resolution,[],[f109,f127])).
% 1.87/0.62  % SZS output end Proof for theBenchmark
% 1.87/0.62  % (19201)------------------------------
% 1.87/0.62  % (19201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (19201)Termination reason: Refutation
% 1.87/0.62  
% 1.87/0.62  % (19201)Memory used [KB]: 11385
% 1.87/0.62  % (19201)Time elapsed: 0.191 s
% 1.87/0.62  % (19201)------------------------------
% 1.87/0.62  % (19201)------------------------------
% 1.87/0.62  % (19176)Success in time 0.259 s
%------------------------------------------------------------------------------
