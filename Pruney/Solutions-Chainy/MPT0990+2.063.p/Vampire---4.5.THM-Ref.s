%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:39 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 951 expanded)
%              Number of leaves         :   30 ( 298 expanded)
%              Depth                    :   21
%              Number of atoms          :  748 (8867 expanded)
%              Number of equality atoms :  212 (3036 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f222,f409,f1255,f1290,f1513])).

fof(f1513,plain,
    ( ~ spl5_3
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f1512])).

fof(f1512,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f1508,f81])).

fof(f81,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f64,f63])).

fof(f63,plain,
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

fof(f64,plain,
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
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

fof(f1508,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(backward_demodulation,[],[f1248,f1440])).

fof(f1440,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(backward_demodulation,[],[f178,f1437])).

fof(f1437,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f1297,f404])).

fof(f404,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl5_16
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1297,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f1296,f169])).

fof(f169,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f107,f75])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1296,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f1291,f73])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f1291,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_15 ),
    inference(resolution,[],[f399,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f100,f85])).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f100,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f399,plain,
    ( v2_funct_1(sK3)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl5_15
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f178,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f125,f169])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f93,f85])).

fof(f93,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1248,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1235,f555])).

fof(f555,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f376,f430])).

fof(f430,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f418,f123])).

fof(f123,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f90,f85])).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f418,plain,(
    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(superposition,[],[f123,f413])).

fof(f413,plain,(
    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f281,f392])).

fof(f392,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f391,f70])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f391,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f390,f71])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f390,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f389,f72])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

fof(f389,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f388,f137])).

fof(f137,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f80,f134])).

fof(f134,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f91,f82])).

fof(f82,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f65])).

fof(f388,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f387,f78])).

fof(f78,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f387,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f383])).

fof(f383,plain,
    ( sK1 != sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f368,f76])).

fof(f76,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f368,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f109,f134])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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

fof(f281,plain,(
    k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f280,f168])).

fof(f168,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f107,f72])).

fof(f280,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f278,f70])).

fof(f278,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f127,f78])).

fof(f376,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2)))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f371,f204])).

fof(f204,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f203,f168])).

fof(f203,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f201,f70])).

fof(f201,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f99,f78])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f371,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl5_3 ),
    inference(resolution,[],[f207,f213])).

fof(f213,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl5_3
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f207,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(resolution,[],[f128,f145])).

fof(f145,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(resolution,[],[f104,f133])).

fof(f133,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f86,f84])).

fof(f84,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f102,f85])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f1235,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f716,f1177])).

fof(f1177,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f1167,f1176])).

fof(f1176,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f1147,f308])).

fof(f308,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f116,f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1147,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f77,f822])).

fof(f822,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f815,f70])).

fof(f815,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f340,f72])).

fof(f340,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f335,f73])).

fof(f335,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f118,f75])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f1167,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1166,f70])).

fof(f1166,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1165,f72])).

fof(f1165,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1164,f73])).

fof(f1164,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1150,f75])).

fof(f1150,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f120,f822])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f716,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f711,f274])).

fof(f274,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(forward_demodulation,[],[f273,f256])).

fof(f256,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f251,f76])).

fof(f251,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f108,f72])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f273,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f272,f168])).

fof(f272,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f270,f70])).

fof(f270,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f126,f78])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f101,f85])).

fof(f101,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f711,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl5_3 ),
    inference(resolution,[],[f708,f213])).

fof(f708,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(k5_relat_1(X8,sK2),sK3) = k5_relat_1(X8,k5_relat_1(sK2,sK3)) ) ),
    inference(resolution,[],[f290,f168])).

fof(f290,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X14,X15),sK3) = k5_relat_1(X14,k5_relat_1(X15,sK3))
      | ~ v1_relat_1(X14) ) ),
    inference(resolution,[],[f95,f169])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f1290,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f1289])).

fof(f1289,plain,
    ( $false
    | spl5_17 ),
    inference(subsumption_resolution,[],[f408,f522])).

fof(f522,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f252,f521])).

fof(f521,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f520,f73])).

fof(f520,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f519,f74])).

fof(f74,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f519,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f518,f75])).

fof(f518,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f517,f70])).

fof(f517,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f516,f71])).

fof(f516,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f515,f72])).

fof(f515,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f111,f77])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f252,plain,(
    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f108,f75])).

fof(f408,plain,
    ( sK0 != k2_relat_1(sK3)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl5_17
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1255,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f1254])).

fof(f1254,plain,
    ( $false
    | spl5_15 ),
    inference(subsumption_resolution,[],[f1242,f122])).

fof(f122,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f83,f85])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f1242,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl5_15 ),
    inference(backward_demodulation,[],[f1157,f1177])).

fof(f1157,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl5_15 ),
    inference(subsumption_resolution,[],[f1156,f73])).

fof(f1156,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f1155,f74])).

fof(f1155,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f1154,f75])).

fof(f1154,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f1153,f400])).

fof(f400,plain,
    ( ~ v2_funct_1(sK3)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f398])).

fof(f1153,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1148,f138])).

fof(f138,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f79,f134])).

fof(f79,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f65])).

fof(f1148,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | o_0_0_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f569,f822])).

fof(f569,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | o_0_0_xboole_0 = X1
      | v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f568,f70])).

fof(f568,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | o_0_0_xboole_0 = X1
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f567,f71])).

fof(f567,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | o_0_0_xboole_0 = X1
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f566,f72])).

fof(f566,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | o_0_0_xboole_0 = X1
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f561])).

fof(f561,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | v2_funct_1(X0)
      | o_0_0_xboole_0 = X1
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f537,f76])).

fof(f537,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | v2_funct_1(X4)
      | o_0_0_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(forward_demodulation,[],[f114,f134])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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

fof(f409,plain,
    ( ~ spl5_15
    | spl5_16
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f396,f406,f402,f398])).

fof(f396,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f395,f73])).

fof(f395,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f394,f74])).

fof(f394,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f393,f75])).

fof(f393,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f384,f138])).

fof(f384,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f368,f252])).

fof(f222,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f220,f168])).

fof(f220,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f219,f70])).

fof(f219,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(resolution,[],[f214,f96])).

fof(f96,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f214,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (1948)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.48  % (1940)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.49  % (1928)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (1938)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (1946)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (1922)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (1923)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (1936)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (1954)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (1937)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (1931)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (1952)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (1947)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (1944)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (1950)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (1939)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (1925)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (1951)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (1924)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (1927)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (1930)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (1949)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (1942)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (1943)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (1941)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (1933)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (1953)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (1934)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (1941)Refutation not found, incomplete strategy% (1941)------------------------------
% 0.20/0.55  % (1941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (1941)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (1941)Memory used [KB]: 10746
% 0.20/0.55  % (1941)Time elapsed: 0.140 s
% 0.20/0.55  % (1941)------------------------------
% 0.20/0.55  % (1941)------------------------------
% 0.20/0.55  % (1932)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (1945)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.09/0.66  % (1930)Refutation found. Thanks to Tanya!
% 2.09/0.66  % SZS status Theorem for theBenchmark
% 2.09/0.66  % SZS output start Proof for theBenchmark
% 2.09/0.66  fof(f1515,plain,(
% 2.09/0.66    $false),
% 2.09/0.66    inference(avatar_sat_refutation,[],[f222,f409,f1255,f1290,f1513])).
% 2.09/0.66  fof(f1513,plain,(
% 2.09/0.66    ~spl5_3 | ~spl5_15 | ~spl5_16),
% 2.09/0.66    inference(avatar_contradiction_clause,[],[f1512])).
% 2.09/0.66  fof(f1512,plain,(
% 2.09/0.66    $false | (~spl5_3 | ~spl5_15 | ~spl5_16)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1508,f81])).
% 2.09/0.66  fof(f81,plain,(
% 2.09/0.66    k2_funct_1(sK2) != sK3),
% 2.09/0.66    inference(cnf_transformation,[],[f65])).
% 2.09/0.66  fof(f65,plain,(
% 2.09/0.66    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.09/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f64,f63])).
% 2.09/0.66  fof(f63,plain,(
% 2.09/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.09/0.66    introduced(choice_axiom,[])).
% 2.09/0.66  fof(f64,plain,(
% 2.09/0.66    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.09/0.66    introduced(choice_axiom,[])).
% 2.09/0.66  fof(f32,plain,(
% 2.09/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.09/0.66    inference(flattening,[],[f31])).
% 2.09/0.67  fof(f31,plain,(
% 2.09/0.67    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.09/0.67    inference(ennf_transformation,[],[f30])).
% 2.09/0.67  fof(f30,negated_conjecture,(
% 2.09/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.09/0.67    inference(negated_conjecture,[],[f29])).
% 2.09/0.67  fof(f29,conjecture,(
% 2.09/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.09/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.09/0.67  fof(f1508,plain,(
% 2.09/0.67    k2_funct_1(sK2) = sK3 | (~spl5_3 | ~spl5_15 | ~spl5_16)),
% 2.09/0.67    inference(backward_demodulation,[],[f1248,f1440])).
% 2.09/0.67  fof(f1440,plain,(
% 2.09/0.67    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl5_15 | ~spl5_16)),
% 2.09/0.67    inference(backward_demodulation,[],[f178,f1437])).
% 2.09/0.67  fof(f1437,plain,(
% 2.09/0.67    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | (~spl5_15 | ~spl5_16)),
% 2.09/0.67    inference(forward_demodulation,[],[f1297,f404])).
% 2.09/0.67  fof(f404,plain,(
% 2.09/0.67    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl5_16),
% 2.09/0.67    inference(avatar_component_clause,[],[f402])).
% 2.09/0.67  fof(f402,plain,(
% 2.09/0.67    spl5_16 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.09/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.09/0.67  fof(f1297,plain,(
% 2.09/0.67    k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl5_15),
% 2.09/0.67    inference(subsumption_resolution,[],[f1296,f169])).
% 2.09/0.67  fof(f169,plain,(
% 2.09/0.67    v1_relat_1(sK3)),
% 2.09/0.67    inference(resolution,[],[f107,f75])).
% 2.09/0.68  fof(f75,plain,(
% 2.09/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f107,plain,(
% 2.09/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f49])).
% 2.09/0.68  fof(f49,plain,(
% 2.09/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.68    inference(ennf_transformation,[],[f19])).
% 2.09/0.68  fof(f19,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.09/0.68  fof(f1296,plain,(
% 2.09/0.68    k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl5_15),
% 2.09/0.68    inference(subsumption_resolution,[],[f1291,f73])).
% 2.09/0.68  fof(f73,plain,(
% 2.09/0.68    v1_funct_1(sK3)),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f1291,plain,(
% 2.09/0.68    k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_15),
% 2.09/0.68    inference(resolution,[],[f399,f127])).
% 2.09/0.68  fof(f127,plain,(
% 2.09/0.68    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/0.68    inference(definition_unfolding,[],[f100,f85])).
% 2.09/0.68  fof(f85,plain,(
% 2.09/0.68    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f25])).
% 2.09/0.68  fof(f25,axiom,(
% 2.09/0.68    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.09/0.68  fof(f100,plain,(
% 2.09/0.68    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f43])).
% 2.09/0.68  fof(f43,plain,(
% 2.09/0.68    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/0.68    inference(flattening,[],[f42])).
% 2.09/0.68  fof(f42,plain,(
% 2.09/0.68    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.09/0.68    inference(ennf_transformation,[],[f18])).
% 2.09/0.68  fof(f18,axiom,(
% 2.09/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.09/0.68  fof(f399,plain,(
% 2.09/0.68    v2_funct_1(sK3) | ~spl5_15),
% 2.09/0.68    inference(avatar_component_clause,[],[f398])).
% 2.09/0.68  fof(f398,plain,(
% 2.09/0.68    spl5_15 <=> v2_funct_1(sK3)),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.09/0.68  fof(f178,plain,(
% 2.09/0.68    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 2.09/0.68    inference(resolution,[],[f125,f169])).
% 2.09/0.68  fof(f125,plain,(
% 2.09/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 2.09/0.68    inference(definition_unfolding,[],[f93,f85])).
% 2.09/0.68  fof(f93,plain,(
% 2.09/0.68    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f35])).
% 2.09/0.68  fof(f35,plain,(
% 2.09/0.68    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.09/0.68    inference(ennf_transformation,[],[f12])).
% 2.09/0.68  fof(f12,axiom,(
% 2.09/0.68    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.09/0.68  fof(f1248,plain,(
% 2.09/0.68    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl5_3),
% 2.09/0.68    inference(forward_demodulation,[],[f1235,f555])).
% 2.09/0.68  fof(f555,plain,(
% 2.09/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl5_3),
% 2.09/0.68    inference(forward_demodulation,[],[f376,f430])).
% 2.09/0.68  fof(f430,plain,(
% 2.09/0.68    sK0 = k1_relat_1(sK2)),
% 2.09/0.68    inference(forward_demodulation,[],[f418,f123])).
% 2.09/0.68  fof(f123,plain,(
% 2.09/0.68    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.09/0.68    inference(definition_unfolding,[],[f90,f85])).
% 2.09/0.68  fof(f90,plain,(
% 2.09/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.09/0.68    inference(cnf_transformation,[],[f11])).
% 2.09/0.68  fof(f11,axiom,(
% 2.09/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.09/0.68  fof(f418,plain,(
% 2.09/0.68    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))),
% 2.09/0.68    inference(superposition,[],[f123,f413])).
% 2.09/0.68  fof(f413,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 2.09/0.68    inference(backward_demodulation,[],[f281,f392])).
% 2.09/0.68  fof(f392,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.09/0.68    inference(subsumption_resolution,[],[f391,f70])).
% 2.09/0.68  fof(f70,plain,(
% 2.09/0.68    v1_funct_1(sK2)),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f391,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f390,f71])).
% 2.09/0.68  fof(f71,plain,(
% 2.09/0.68    v1_funct_2(sK2,sK0,sK1)),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f390,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f389,f72])).
% 2.09/0.68  fof(f72,plain,(
% 2.09/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f389,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f388,f137])).
% 2.09/0.68  fof(f137,plain,(
% 2.09/0.68    o_0_0_xboole_0 != sK1),
% 2.09/0.68    inference(backward_demodulation,[],[f80,f134])).
% 2.09/0.68  fof(f134,plain,(
% 2.09/0.68    o_0_0_xboole_0 = k1_xboole_0),
% 2.09/0.68    inference(resolution,[],[f91,f82])).
% 2.09/0.68  fof(f82,plain,(
% 2.09/0.68    v1_xboole_0(o_0_0_xboole_0)),
% 2.09/0.68    inference(cnf_transformation,[],[f1])).
% 2.09/0.68  fof(f1,axiom,(
% 2.09/0.68    v1_xboole_0(o_0_0_xboole_0)),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 2.09/0.68  fof(f91,plain,(
% 2.09/0.68    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.09/0.68    inference(cnf_transformation,[],[f33])).
% 2.09/0.68  fof(f33,plain,(
% 2.09/0.68    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.09/0.68    inference(ennf_transformation,[],[f2])).
% 2.09/0.68  fof(f2,axiom,(
% 2.09/0.68    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.09/0.68  fof(f80,plain,(
% 2.09/0.68    k1_xboole_0 != sK1),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f388,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | o_0_0_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f387,f78])).
% 2.09/0.68  fof(f78,plain,(
% 2.09/0.68    v2_funct_1(sK2)),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f387,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v2_funct_1(sK2) | o_0_0_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(trivial_inequality_removal,[],[f383])).
% 2.09/0.68  fof(f383,plain,(
% 2.09/0.68    sK1 != sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v2_funct_1(sK2) | o_0_0_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(superposition,[],[f368,f76])).
% 2.09/0.68  fof(f76,plain,(
% 2.09/0.68    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f368,plain,(
% 2.09/0.68    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v2_funct_1(X2) | o_0_0_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.09/0.68    inference(forward_demodulation,[],[f109,f134])).
% 2.09/0.68  fof(f109,plain,(
% 2.09/0.68    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f52])).
% 2.09/0.68  fof(f52,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.09/0.68    inference(flattening,[],[f51])).
% 2.09/0.68  fof(f51,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.09/0.68    inference(ennf_transformation,[],[f28])).
% 2.09/0.68  fof(f28,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.09/0.68  fof(f281,plain,(
% 2.09/0.68    k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.09/0.68    inference(subsumption_resolution,[],[f280,f168])).
% 2.09/0.68  fof(f168,plain,(
% 2.09/0.68    v1_relat_1(sK2)),
% 2.09/0.68    inference(resolution,[],[f107,f72])).
% 2.09/0.68  fof(f280,plain,(
% 2.09/0.68    k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f278,f70])).
% 2.09/0.68  fof(f278,plain,(
% 2.09/0.68    k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.09/0.68    inference(resolution,[],[f127,f78])).
% 2.09/0.68  fof(f376,plain,(
% 2.09/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) | ~spl5_3),
% 2.09/0.68    inference(forward_demodulation,[],[f371,f204])).
% 2.09/0.68  fof(f204,plain,(
% 2.09/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.09/0.68    inference(subsumption_resolution,[],[f203,f168])).
% 2.09/0.68  fof(f203,plain,(
% 2.09/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f201,f70])).
% 2.09/0.68  fof(f201,plain,(
% 2.09/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.09/0.68    inference(resolution,[],[f99,f78])).
% 2.09/0.68  fof(f99,plain,(
% 2.09/0.68    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f41])).
% 2.09/0.68  fof(f41,plain,(
% 2.09/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/0.68    inference(flattening,[],[f40])).
% 2.09/0.68  fof(f40,plain,(
% 2.09/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.09/0.68    inference(ennf_transformation,[],[f17])).
% 2.09/0.68  fof(f17,axiom,(
% 2.09/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.09/0.68  fof(f371,plain,(
% 2.09/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl5_3),
% 2.09/0.68    inference(resolution,[],[f207,f213])).
% 2.09/0.68  fof(f213,plain,(
% 2.09/0.68    v1_relat_1(k2_funct_1(sK2)) | ~spl5_3),
% 2.09/0.68    inference(avatar_component_clause,[],[f212])).
% 2.09/0.68  fof(f212,plain,(
% 2.09/0.68    spl5_3 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.09/0.68  fof(f207,plain,(
% 2.09/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.09/0.68    inference(resolution,[],[f128,f145])).
% 2.09/0.68  fof(f145,plain,(
% 2.09/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.09/0.68    inference(resolution,[],[f104,f133])).
% 2.09/0.68  fof(f133,plain,(
% 2.09/0.68    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.09/0.68    inference(forward_demodulation,[],[f86,f84])).
% 2.09/0.68  fof(f84,plain,(
% 2.09/0.68    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.09/0.68    inference(cnf_transformation,[],[f5])).
% 2.09/0.68  fof(f5,axiom,(
% 2.09/0.68    ! [X0] : k2_subset_1(X0) = X0),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.09/0.68  fof(f86,plain,(
% 2.09/0.68    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.09/0.68    inference(cnf_transformation,[],[f6])).
% 2.09/0.68  fof(f6,axiom,(
% 2.09/0.68    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.09/0.68  fof(f104,plain,(
% 2.09/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f66])).
% 2.09/0.68  fof(f66,plain,(
% 2.09/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.09/0.68    inference(nnf_transformation,[],[f7])).
% 2.09/0.68  fof(f7,axiom,(
% 2.09/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.09/0.68  fof(f128,plain,(
% 2.09/0.68    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 2.09/0.68    inference(definition_unfolding,[],[f102,f85])).
% 2.09/0.68  fof(f102,plain,(
% 2.09/0.68    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f45])).
% 2.09/0.68  fof(f45,plain,(
% 2.09/0.68    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.09/0.68    inference(flattening,[],[f44])).
% 2.09/0.68  fof(f44,plain,(
% 2.09/0.68    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.09/0.68    inference(ennf_transformation,[],[f13])).
% 2.09/0.68  fof(f13,axiom,(
% 2.09/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.09/0.68  fof(f1235,plain,(
% 2.09/0.68    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl5_3),
% 2.09/0.68    inference(backward_demodulation,[],[f716,f1177])).
% 2.09/0.68  fof(f1177,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.09/0.68    inference(global_subsumption,[],[f1167,f1176])).
% 2.09/0.68  fof(f1176,plain,(
% 2.09/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.09/0.68    inference(resolution,[],[f1147,f308])).
% 2.09/0.68  fof(f308,plain,(
% 2.09/0.68    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.09/0.68    inference(resolution,[],[f116,f88])).
% 2.09/0.68  fof(f88,plain,(
% 2.09/0.68    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.09/0.68    inference(cnf_transformation,[],[f23])).
% 2.09/0.68  fof(f23,axiom,(
% 2.09/0.68    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.09/0.68  fof(f116,plain,(
% 2.09/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.68    inference(cnf_transformation,[],[f67])).
% 2.09/0.68  fof(f67,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.68    inference(nnf_transformation,[],[f58])).
% 2.09/0.68  fof(f58,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.68    inference(flattening,[],[f57])).
% 2.09/0.68  fof(f57,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.09/0.68    inference(ennf_transformation,[],[f21])).
% 2.09/0.68  fof(f21,axiom,(
% 2.09/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.09/0.68  fof(f1147,plain,(
% 2.09/0.68    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.09/0.68    inference(backward_demodulation,[],[f77,f822])).
% 2.09/0.68  fof(f822,plain,(
% 2.09/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f815,f70])).
% 2.09/0.68  fof(f815,plain,(
% 2.09/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(resolution,[],[f340,f72])).
% 2.09/0.68  fof(f340,plain,(
% 2.09/0.68    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 2.09/0.68    inference(subsumption_resolution,[],[f335,f73])).
% 2.09/0.68  fof(f335,plain,(
% 2.09/0.68    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 2.09/0.68    inference(resolution,[],[f118,f75])).
% 2.09/0.68  fof(f118,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f60])).
% 2.09/0.68  fof(f60,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.09/0.68    inference(flattening,[],[f59])).
% 2.09/0.68  fof(f59,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.09/0.68    inference(ennf_transformation,[],[f24])).
% 2.09/0.68  fof(f24,axiom,(
% 2.09/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.09/0.68  fof(f77,plain,(
% 2.09/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f1167,plain,(
% 2.09/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.09/0.68    inference(subsumption_resolution,[],[f1166,f70])).
% 2.09/0.68  fof(f1166,plain,(
% 2.09/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f1165,f72])).
% 2.09/0.68  fof(f1165,plain,(
% 2.09/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f1164,f73])).
% 2.09/0.68  fof(f1164,plain,(
% 2.09/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f1150,f75])).
% 2.09/0.68  fof(f1150,plain,(
% 2.09/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.09/0.68    inference(superposition,[],[f120,f822])).
% 2.09/0.68  fof(f120,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f62])).
% 2.09/0.68  fof(f62,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.09/0.68    inference(flattening,[],[f61])).
% 2.09/0.68  fof(f61,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.09/0.68    inference(ennf_transformation,[],[f22])).
% 2.09/0.68  fof(f22,axiom,(
% 2.09/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.09/0.68  fof(f716,plain,(
% 2.09/0.68    k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl5_3),
% 2.09/0.68    inference(forward_demodulation,[],[f711,f274])).
% 2.09/0.68  fof(f274,plain,(
% 2.09/0.68    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.09/0.68    inference(forward_demodulation,[],[f273,f256])).
% 2.09/0.68  fof(f256,plain,(
% 2.09/0.68    sK1 = k2_relat_1(sK2)),
% 2.09/0.68    inference(forward_demodulation,[],[f251,f76])).
% 2.09/0.68  fof(f251,plain,(
% 2.09/0.68    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.09/0.68    inference(resolution,[],[f108,f72])).
% 2.09/0.68  fof(f108,plain,(
% 2.09/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f50])).
% 2.09/0.68  fof(f50,plain,(
% 2.09/0.68    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.68    inference(ennf_transformation,[],[f20])).
% 2.09/0.68  fof(f20,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.09/0.68  fof(f273,plain,(
% 2.09/0.68    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f272,f168])).
% 2.09/0.68  fof(f272,plain,(
% 2.09/0.68    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 2.09/0.68    inference(subsumption_resolution,[],[f270,f70])).
% 2.09/0.68  fof(f270,plain,(
% 2.09/0.68    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.09/0.68    inference(resolution,[],[f126,f78])).
% 2.09/0.68  fof(f126,plain,(
% 2.09/0.68    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/0.68    inference(definition_unfolding,[],[f101,f85])).
% 2.09/0.68  fof(f101,plain,(
% 2.09/0.68    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f43])).
% 2.09/0.68  fof(f711,plain,(
% 2.09/0.68    k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) | ~spl5_3),
% 2.09/0.68    inference(resolution,[],[f708,f213])).
% 2.09/0.68  fof(f708,plain,(
% 2.09/0.68    ( ! [X8] : (~v1_relat_1(X8) | k5_relat_1(k5_relat_1(X8,sK2),sK3) = k5_relat_1(X8,k5_relat_1(sK2,sK3))) )),
% 2.09/0.68    inference(resolution,[],[f290,f168])).
% 2.09/0.68  fof(f290,plain,(
% 2.09/0.68    ( ! [X14,X15] : (~v1_relat_1(X15) | k5_relat_1(k5_relat_1(X14,X15),sK3) = k5_relat_1(X14,k5_relat_1(X15,sK3)) | ~v1_relat_1(X14)) )),
% 2.09/0.68    inference(resolution,[],[f95,f169])).
% 2.09/0.68  fof(f95,plain,(
% 2.09/0.68    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f37])).
% 2.09/0.68  fof(f37,plain,(
% 2.09/0.68    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.09/0.68    inference(ennf_transformation,[],[f10])).
% 2.09/0.68  fof(f10,axiom,(
% 2.09/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.09/0.68  fof(f1290,plain,(
% 2.09/0.68    spl5_17),
% 2.09/0.68    inference(avatar_contradiction_clause,[],[f1289])).
% 2.09/0.68  fof(f1289,plain,(
% 2.09/0.68    $false | spl5_17),
% 2.09/0.68    inference(subsumption_resolution,[],[f408,f522])).
% 2.09/0.68  fof(f522,plain,(
% 2.09/0.68    sK0 = k2_relat_1(sK3)),
% 2.09/0.68    inference(backward_demodulation,[],[f252,f521])).
% 2.09/0.68  fof(f521,plain,(
% 2.09/0.68    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f520,f73])).
% 2.09/0.68  fof(f520,plain,(
% 2.09/0.68    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f519,f74])).
% 2.09/0.68  fof(f74,plain,(
% 2.09/0.68    v1_funct_2(sK3,sK1,sK0)),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f519,plain,(
% 2.09/0.68    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f518,f75])).
% 2.09/0.68  fof(f518,plain,(
% 2.09/0.68    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f517,f70])).
% 2.09/0.68  fof(f517,plain,(
% 2.09/0.68    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f516,f71])).
% 2.09/0.68  fof(f516,plain,(
% 2.09/0.68    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f515,f72])).
% 2.09/0.68  fof(f515,plain,(
% 2.09/0.68    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(resolution,[],[f111,f77])).
% 2.09/0.68  fof(f111,plain,(
% 2.09/0.68    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f54])).
% 2.09/0.68  fof(f54,plain,(
% 2.09/0.68    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.09/0.68    inference(flattening,[],[f53])).
% 2.09/0.68  fof(f53,plain,(
% 2.09/0.68    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.09/0.68    inference(ennf_transformation,[],[f26])).
% 2.09/0.68  fof(f26,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.09/0.68  fof(f252,plain,(
% 2.09/0.68    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)),
% 2.09/0.68    inference(resolution,[],[f108,f75])).
% 2.09/0.68  fof(f408,plain,(
% 2.09/0.68    sK0 != k2_relat_1(sK3) | spl5_17),
% 2.09/0.68    inference(avatar_component_clause,[],[f406])).
% 2.09/0.68  fof(f406,plain,(
% 2.09/0.68    spl5_17 <=> sK0 = k2_relat_1(sK3)),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.09/0.68  fof(f1255,plain,(
% 2.09/0.68    spl5_15),
% 2.09/0.68    inference(avatar_contradiction_clause,[],[f1254])).
% 2.09/0.68  fof(f1254,plain,(
% 2.09/0.68    $false | spl5_15),
% 2.09/0.68    inference(subsumption_resolution,[],[f1242,f122])).
% 2.09/0.68  fof(f122,plain,(
% 2.09/0.68    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.09/0.68    inference(definition_unfolding,[],[f83,f85])).
% 2.09/0.68  fof(f83,plain,(
% 2.09/0.68    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.09/0.68    inference(cnf_transformation,[],[f16])).
% 2.09/0.68  fof(f16,axiom,(
% 2.09/0.68    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 2.09/0.68  fof(f1242,plain,(
% 2.09/0.68    ~v2_funct_1(k6_partfun1(sK0)) | spl5_15),
% 2.09/0.68    inference(backward_demodulation,[],[f1157,f1177])).
% 2.09/0.68  fof(f1157,plain,(
% 2.09/0.68    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl5_15),
% 2.09/0.68    inference(subsumption_resolution,[],[f1156,f73])).
% 2.09/0.68  fof(f1156,plain,(
% 2.09/0.68    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | spl5_15),
% 2.09/0.68    inference(subsumption_resolution,[],[f1155,f74])).
% 2.09/0.68  fof(f1155,plain,(
% 2.09/0.68    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl5_15),
% 2.09/0.68    inference(subsumption_resolution,[],[f1154,f75])).
% 2.09/0.68  fof(f1154,plain,(
% 2.09/0.68    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl5_15),
% 2.09/0.68    inference(subsumption_resolution,[],[f1153,f400])).
% 2.09/0.68  fof(f400,plain,(
% 2.09/0.68    ~v2_funct_1(sK3) | spl5_15),
% 2.09/0.68    inference(avatar_component_clause,[],[f398])).
% 2.09/0.68  fof(f1153,plain,(
% 2.09/0.68    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f1148,f138])).
% 2.09/0.68  fof(f138,plain,(
% 2.09/0.68    o_0_0_xboole_0 != sK0),
% 2.09/0.68    inference(backward_demodulation,[],[f79,f134])).
% 2.09/0.68  fof(f79,plain,(
% 2.09/0.68    k1_xboole_0 != sK0),
% 2.09/0.68    inference(cnf_transformation,[],[f65])).
% 2.09/0.68  fof(f1148,plain,(
% 2.09/0.68    ~v2_funct_1(k5_relat_1(sK2,sK3)) | o_0_0_xboole_0 = sK0 | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(superposition,[],[f569,f822])).
% 2.09/0.68  fof(f569,plain,(
% 2.09/0.68    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | o_0_0_xboole_0 = X1 | v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1) | ~v1_funct_1(X0)) )),
% 2.09/0.68    inference(subsumption_resolution,[],[f568,f70])).
% 2.09/0.68  fof(f568,plain,(
% 2.09/0.68    ( ! [X0,X1] : (v2_funct_1(X0) | o_0_0_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1) | ~v1_funct_1(X0) | ~v1_funct_1(sK2)) )),
% 2.09/0.68    inference(subsumption_resolution,[],[f567,f71])).
% 2.09/0.68  fof(f567,plain,(
% 2.09/0.68    ( ! [X0,X1] : (v2_funct_1(X0) | o_0_0_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1) | ~v1_funct_1(X0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.09/0.68    inference(subsumption_resolution,[],[f566,f72])).
% 2.09/0.68  fof(f566,plain,(
% 2.09/0.68    ( ! [X0,X1] : (v2_funct_1(X0) | o_0_0_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1) | ~v1_funct_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.09/0.68    inference(trivial_inequality_removal,[],[f561])).
% 2.09/0.68  fof(f561,plain,(
% 2.09/0.68    ( ! [X0,X1] : (sK1 != sK1 | v2_funct_1(X0) | o_0_0_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1) | ~v1_funct_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.09/0.68    inference(superposition,[],[f537,f76])).
% 2.09/0.68  fof(f537,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | v2_funct_1(X4) | o_0_0_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.09/0.68    inference(forward_demodulation,[],[f114,f134])).
% 2.09/0.68  fof(f114,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f56])).
% 2.09/0.68  fof(f56,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.09/0.68    inference(flattening,[],[f55])).
% 2.09/0.68  fof(f55,plain,(
% 2.09/0.68    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.09/0.68    inference(ennf_transformation,[],[f27])).
% 2.09/0.68  fof(f27,axiom,(
% 2.09/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.09/0.68  fof(f409,plain,(
% 2.09/0.68    ~spl5_15 | spl5_16 | ~spl5_17),
% 2.09/0.68    inference(avatar_split_clause,[],[f396,f406,f402,f398])).
% 2.09/0.68  fof(f396,plain,(
% 2.09/0.68    sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f395,f73])).
% 2.09/0.68  fof(f395,plain,(
% 2.09/0.68    sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f394,f74])).
% 2.09/0.68  fof(f394,plain,(
% 2.09/0.68    sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f393,f75])).
% 2.09/0.68  fof(f393,plain,(
% 2.09/0.68    sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(subsumption_resolution,[],[f384,f138])).
% 2.09/0.68  fof(f384,plain,(
% 2.09/0.68    sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.09/0.68    inference(superposition,[],[f368,f252])).
% 2.09/0.68  fof(f222,plain,(
% 2.09/0.68    spl5_3),
% 2.09/0.68    inference(avatar_contradiction_clause,[],[f221])).
% 2.09/0.68  fof(f221,plain,(
% 2.09/0.68    $false | spl5_3),
% 2.09/0.68    inference(subsumption_resolution,[],[f220,f168])).
% 2.09/0.68  fof(f220,plain,(
% 2.09/0.68    ~v1_relat_1(sK2) | spl5_3),
% 2.09/0.68    inference(subsumption_resolution,[],[f219,f70])).
% 2.09/0.68  fof(f219,plain,(
% 2.09/0.68    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_3),
% 2.09/0.68    inference(resolution,[],[f214,f96])).
% 2.09/0.68  fof(f96,plain,(
% 2.09/0.68    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f39])).
% 2.09/0.68  fof(f39,plain,(
% 2.09/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/0.68    inference(flattening,[],[f38])).
% 2.09/0.68  fof(f38,plain,(
% 2.09/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.09/0.68    inference(ennf_transformation,[],[f14])).
% 2.09/0.68  fof(f14,axiom,(
% 2.09/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.09/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.09/0.68  fof(f214,plain,(
% 2.09/0.68    ~v1_relat_1(k2_funct_1(sK2)) | spl5_3),
% 2.09/0.68    inference(avatar_component_clause,[],[f212])).
% 2.09/0.68  % SZS output end Proof for theBenchmark
% 2.09/0.68  % (1930)------------------------------
% 2.09/0.68  % (1930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.68  % (1930)Termination reason: Refutation
% 2.09/0.68  
% 2.09/0.68  % (1930)Memory used [KB]: 12281
% 2.09/0.68  % (1930)Time elapsed: 0.226 s
% 2.09/0.68  % (1930)------------------------------
% 2.09/0.68  % (1930)------------------------------
% 2.09/0.68  % (1921)Success in time 0.327 s
%------------------------------------------------------------------------------
