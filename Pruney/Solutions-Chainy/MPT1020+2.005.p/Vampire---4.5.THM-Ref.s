%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:40 EST 2020

% Result     : Theorem 3.94s
% Output     : Refutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  303 (1571 expanded)
%              Number of leaves         :   45 ( 501 expanded)
%              Depth                    :   21
%              Number of atoms          : 1113 (12070 expanded)
%              Number of equality atoms :  202 ( 407 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f236,f355,f373,f423,f449,f479,f956,f1604,f1759,f1779,f1823,f1897,f1932,f2656,f2980,f3184,f3190,f3458,f3468,f3478,f4142])).

fof(f4142,plain,
    ( ~ spl5_13
    | ~ spl5_57
    | ~ spl5_96
    | ~ spl5_119 ),
    inference(avatar_contradiction_clause,[],[f4141])).

fof(f4141,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_57
    | ~ spl5_96
    | ~ spl5_119 ),
    inference(subsumption_resolution,[],[f4140,f3140])).

fof(f3140,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f1548,f342])).

fof(f342,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl5_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1548,plain,
    ( r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f1546])).

fof(f1546,plain,
    ( spl5_57
  <=> r2_relset_1(sK0,sK0,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f4140,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_57
    | ~ spl5_96
    | ~ spl5_119 ),
    inference(forward_demodulation,[],[f4139,f3857])).

fof(f3857,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_57
    | ~ spl5_96
    | ~ spl5_119 ),
    inference(forward_demodulation,[],[f3856,f3758])).

fof(f3758,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_13
    | ~ spl5_57
    | ~ spl5_96 ),
    inference(forward_demodulation,[],[f3757,f3663])).

fof(f3663,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f3662,f3362])).

fof(f3362,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13 ),
    inference(superposition,[],[f78,f342])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f64,f63])).

fof(f63,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f3662,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f3661,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3661,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(resolution,[],[f3140,f110])).

fof(f110,plain,(
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
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f3757,plain,
    ( sK1 = sK2
    | ~ spl5_13
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f3756,f3362])).

fof(f3756,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f3754,f3359])).

fof(f3359,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13 ),
    inference(superposition,[],[f74,f342])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f3754,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13
    | ~ spl5_96 ),
    inference(resolution,[],[f3315,f110])).

fof(f3315,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK1)
    | ~ spl5_13
    | ~ spl5_96 ),
    inference(forward_demodulation,[],[f1741,f342])).

fof(f1741,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK1)
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f1739])).

fof(f1739,plain,
    ( spl5_96
  <=> r2_relset_1(sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f3856,plain,
    ( sK1 = k2_funct_1(sK1)
    | ~ spl5_13
    | ~ spl5_119 ),
    inference(subsumption_resolution,[],[f3855,f3388])).

fof(f3388,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13 ),
    inference(superposition,[],[f293,f342])).

fof(f293,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f292,f250])).

fof(f250,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f249,f71])).

fof(f71,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f249,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f248,f72])).

fof(f72,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f248,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f243,f73])).

fof(f73,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f243,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f91,f74])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f292,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f291,f71])).

fof(f291,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f290,f72])).

fof(f290,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f285,f73])).

fof(f285,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f95,f74])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f3855,plain,
    ( sK1 = k2_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13
    | ~ spl5_119 ),
    inference(subsumption_resolution,[],[f3853,f3359])).

fof(f3853,plain,
    ( sK1 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_13
    | ~ spl5_119 ),
    inference(resolution,[],[f3307,f110])).

fof(f3307,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1)
    | ~ spl5_13
    | ~ spl5_119 ),
    inference(forward_demodulation,[],[f1931,f342])).

fof(f1931,plain,
    ( r2_relset_1(sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl5_119 ),
    inference(avatar_component_clause,[],[f1929])).

fof(f1929,plain,
    ( spl5_119
  <=> r2_relset_1(sK0,sK0,k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f4139,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl5_13
    | ~ spl5_57
    | ~ spl5_96 ),
    inference(forward_demodulation,[],[f4136,f3739])).

fof(f3739,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f3705,f342])).

fof(f3705,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(sK0,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(superposition,[],[f253,f3663])).

fof(f253,plain,(
    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f252,f75])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f252,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f251,f76])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f251,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f244,f77])).

fof(f77,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f244,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f91,f78])).

fof(f4136,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl5_13
    | ~ spl5_57
    | ~ spl5_96 ),
    inference(superposition,[],[f3364,f3758])).

fof(f3364,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_2(k1_xboole_0,sK1))
    | ~ spl5_13 ),
    inference(superposition,[],[f80,f342])).

fof(f80,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f3478,plain,
    ( ~ spl5_13
    | ~ spl5_20
    | ~ spl5_118 ),
    inference(avatar_contradiction_clause,[],[f3477])).

fof(f3477,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_20
    | ~ spl5_118 ),
    inference(subsumption_resolution,[],[f3422,f448])).

fof(f448,plain,
    ( ! [X5] : ~ r2_hidden(X5,k1_xboole_0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl5_20
  <=> ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f3422,plain,
    ( r2_hidden(sK4(k1_xboole_0,k2_funct_1(sK1),sK1),k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_118 ),
    inference(superposition,[],[f1927,f342])).

fof(f1927,plain,
    ( r2_hidden(sK4(sK0,k2_funct_1(sK1),sK1),sK0)
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f1925])).

fof(f1925,plain,
    ( spl5_118
  <=> r2_hidden(sK4(sK0,k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f3468,plain,
    ( ~ spl5_13
    | ~ spl5_20
    | ~ spl5_111 ),
    inference(avatar_contradiction_clause,[],[f3467])).

fof(f3467,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_20
    | ~ spl5_111 ),
    inference(subsumption_resolution,[],[f3416,f448])).

fof(f3416,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK2,sK1),k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_111 ),
    inference(superposition,[],[f1821,f342])).

fof(f1821,plain,
    ( r2_hidden(sK4(sK0,sK2,sK1),sK0)
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f1819])).

fof(f1819,plain,
    ( spl5_111
  <=> r2_hidden(sK4(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f3458,plain,
    ( ~ spl5_13
    | ~ spl5_20
    | ~ spl5_99 ),
    inference(avatar_contradiction_clause,[],[f3457])).

fof(f3457,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_20
    | ~ spl5_99 ),
    inference(subsumption_resolution,[],[f3411,f448])).

fof(f3411,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_relat_1(k1_xboole_0),sK2),k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_99 ),
    inference(superposition,[],[f1758,f342])).

fof(f1758,plain,
    ( r2_hidden(sK4(sK0,k1_relat_1(k1_xboole_0),sK2),sK0)
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f1756])).

fof(f1756,plain,
    ( spl5_99
  <=> r2_hidden(sK4(sK0,k1_relat_1(k1_xboole_0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f3190,plain,
    ( ~ spl5_13
    | ~ spl5_20
    | ~ spl5_67 ),
    inference(avatar_contradiction_clause,[],[f3189])).

fof(f3189,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_20
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f3188,f448])).

fof(f3188,plain,
    ( r2_hidden(sK4(k1_xboole_0,k2_funct_1(sK2),k1_xboole_0),k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_67 ),
    inference(forward_demodulation,[],[f1603,f342])).

fof(f1603,plain,
    ( r2_hidden(sK4(sK0,k2_funct_1(sK2),k1_xboole_0),sK0)
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f1601])).

fof(f1601,plain,
    ( spl5_67
  <=> r2_hidden(sK4(sK0,k2_funct_1(sK2),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f3184,plain,
    ( ~ spl5_13
    | ~ spl5_20
    | ~ spl5_103 ),
    inference(avatar_contradiction_clause,[],[f3183])).

fof(f3183,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_20
    | ~ spl5_103 ),
    inference(subsumption_resolution,[],[f3182,f448])).

fof(f3182,plain,
    ( r2_hidden(sK4(k1_xboole_0,k2_funct_1(sK2),sK2),k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_103 ),
    inference(forward_demodulation,[],[f1778,f342])).

fof(f1778,plain,
    ( r2_hidden(sK4(sK0,k2_funct_1(sK2),sK2),sK0)
    | ~ spl5_103 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f1776,plain,
    ( spl5_103
  <=> r2_hidden(sK4(sK0,k2_funct_1(sK2),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f2980,plain,
    ( ~ spl5_10
    | spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f2979])).

fof(f2979,plain,
    ( $false
    | ~ spl5_10
    | spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f2978,f2961])).

fof(f2961,plain,
    ( sK0 != k2_relat_1(k6_partfun1(sK0))
    | ~ spl5_10
    | spl5_12
    | spl5_13
    | ~ spl5_25 ),
    inference(superposition,[],[f2184,f170])).

fof(f170,plain,(
    ! [X0] : k2_relset_1(X0,X0,k6_partfun1(X0)) = k2_relat_1(k6_partfun1(X0)) ),
    inference(resolution,[],[f99,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2184,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_partfun1(sK0))
    | ~ spl5_10
    | spl5_12
    | spl5_13
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f2183,f235])).

fof(f235,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl5_10
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f2183,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2))
    | spl5_12
    | spl5_13
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f2182,f2001])).

fof(f2001,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl5_12
    | spl5_13 ),
    inference(global_subsumption,[],[f338])).

fof(f338,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl5_12
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2182,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f2181,f72])).

fof(f2181,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | sK0 != k2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f2163,f71])).

fof(f2163,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | sK0 != k2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2))
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl5_25 ),
    inference(resolution,[],[f478,f74])).

fof(f478,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,sK0)
        | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2))
        | sK0 = k2_relset_1(X2,sK0,X3) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl5_25
  <=> ! [X3,X2] :
        ( sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
        | sK0 = k2_relset_1(X2,sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f2978,plain,
    ( sK0 = k2_relat_1(k6_partfun1(sK0))
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f2973,f529])).

fof(f529,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(superposition,[],[f212,f164])).

fof(f164,plain,(
    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f98,f78])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f212,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f211,f75])).

fof(f211,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f205,f76])).

fof(f205,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f96,f78])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f2973,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl5_14 ),
    inference(superposition,[],[f301,f350])).

fof(f350,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl5_14
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f301,plain,(
    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f300,f144])).

fof(f144,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f97,f78])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f300,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f298,f75])).

fof(f298,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f191,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f191,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f190,f75])).

fof(f190,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f184,f77])).

fof(f184,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f102,f78])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f2656,plain,
    ( ~ spl5_56
    | spl5_57
    | ~ spl5_73
    | ~ spl5_81 ),
    inference(avatar_contradiction_clause,[],[f2655])).

fof(f2655,plain,
    ( $false
    | ~ spl5_56
    | spl5_57
    | ~ spl5_73
    | ~ spl5_81 ),
    inference(subsumption_resolution,[],[f2654,f1547])).

fof(f1547,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | spl5_57 ),
    inference(avatar_component_clause,[],[f1546])).

fof(f2654,plain,
    ( r2_relset_1(sK0,sK0,sK2,k1_xboole_0)
    | ~ spl5_56
    | ~ spl5_73
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f2624,f2484])).

fof(f2484,plain,
    ( sK2 = k1_relat_1(k1_xboole_0)
    | ~ spl5_73 ),
    inference(subsumption_resolution,[],[f2483,f181])).

fof(f181,plain,(
    ! [X1] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(forward_demodulation,[],[f176,f166])).

fof(f166,plain,(
    ! [X2,X1] : k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f98,f81])).

fof(f176,plain,(
    ! [X2,X1] : m1_subset_1(k1_relset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f100,f81])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f2483,plain,
    ( sK2 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_73 ),
    inference(subsumption_resolution,[],[f2482,f78])).

fof(f2482,plain,
    ( sK2 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_73 ),
    inference(resolution,[],[f1634,f110])).

fof(f1634,plain,
    ( r2_relset_1(sK0,sK0,k1_relat_1(k1_xboole_0),sK2)
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f1632])).

fof(f1632,plain,
    ( spl5_73
  <=> r2_relset_1(sK0,sK0,k1_relat_1(k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f2624,plain,
    ( r2_relset_1(sK0,sK0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_56
    | ~ spl5_73
    | ~ spl5_81 ),
    inference(superposition,[],[f1634,f2492])).

fof(f2492,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_56
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f2491,f2412])).

fof(f2412,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f2411,f297])).

fof(f297,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f296,f253])).

fof(f296,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f295,f75])).

fof(f295,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f294,f76])).

fof(f294,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f286,f77])).

fof(f286,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f95,f78])).

fof(f2411,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f2410,f81])).

fof(f2410,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_56 ),
    inference(resolution,[],[f1541,f110])).

fof(f1541,plain,
    ( r2_relset_1(sK0,sK0,k2_funct_1(sK2),k1_xboole_0)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f1539])).

fof(f1539,plain,
    ( spl5_56
  <=> r2_relset_1(sK0,sK0,k2_funct_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f2491,plain,
    ( sK2 = k2_funct_1(sK2)
    | ~ spl5_81 ),
    inference(subsumption_resolution,[],[f2490,f297])).

fof(f2490,plain,
    ( sK2 = k2_funct_1(sK2)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_81 ),
    inference(subsumption_resolution,[],[f2489,f78])).

fof(f2489,plain,
    ( sK2 = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_81 ),
    inference(resolution,[],[f1670,f110])).

fof(f1670,plain,
    ( r2_relset_1(sK0,sK0,k2_funct_1(sK2),sK2)
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f1668])).

fof(f1668,plain,
    ( spl5_81
  <=> r2_relset_1(sK0,sK0,k2_funct_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f1932,plain,
    ( spl5_118
    | spl5_119 ),
    inference(avatar_split_clause,[],[f849,f1929,f1925])).

fof(f849,plain,
    ( r2_relset_1(sK0,sK0,k2_funct_1(sK1),sK1)
    | r2_hidden(sK4(sK0,k2_funct_1(sK1),sK1),sK0) ),
    inference(resolution,[],[f280,f293])).

fof(f280,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | r2_relset_1(sK0,sK0,X0,sK1)
      | r2_hidden(sK4(sK0,X0,sK1),sK0) ) ),
    inference(resolution,[],[f89,f74])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_relset_1(X0,X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2))
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

fof(f1897,plain,
    ( ~ spl5_12
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f1896])).

fof(f1896,plain,
    ( $false
    | ~ spl5_12
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1895,f159])).

fof(f159,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f115,f78])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f1895,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl5_12
    | spl5_13 ),
    inference(forward_demodulation,[],[f515,f1473])).

fof(f1473,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl5_12
    | spl5_13 ),
    inference(global_subsumption,[],[f341,f1472])).

fof(f1472,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1471,f71])).

fof(f1471,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1470,f72])).

fof(f1470,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1469,f74])).

fof(f1469,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1468,f75])).

fof(f1468,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1467,f76])).

fof(f1467,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1466,f78])).

fof(f1466,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1465,f337])).

fof(f337,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f336])).

fof(f1465,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f391,f189])).

fof(f189,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f188,f71])).

fof(f188,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f183,f73])).

fof(f183,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f102,f74])).

fof(f391,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f106,f79])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = X3
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f341,plain,
    ( k1_xboole_0 != sK0
    | spl5_13 ),
    inference(avatar_component_clause,[],[f340])).

fof(f515,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(superposition,[],[f80,f250])).

fof(f1823,plain,
    ( spl5_111
    | spl5_96 ),
    inference(avatar_split_clause,[],[f848,f1739,f1819])).

fof(f848,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK1)
    | r2_hidden(sK4(sK0,sK2,sK1),sK0) ),
    inference(resolution,[],[f280,f78])).

fof(f1779,plain,
    ( spl5_103
    | spl5_81 ),
    inference(avatar_split_clause,[],[f885,f1668,f1776])).

fof(f885,plain,
    ( r2_relset_1(sK0,sK0,k2_funct_1(sK2),sK2)
    | r2_hidden(sK4(sK0,k2_funct_1(sK2),sK2),sK0) ),
    inference(resolution,[],[f281,f297])).

fof(f281,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | r2_relset_1(sK0,sK0,X1,sK2)
      | r2_hidden(sK4(sK0,X1,sK2),sK0) ) ),
    inference(resolution,[],[f89,f78])).

fof(f1759,plain,
    ( spl5_99
    | spl5_73 ),
    inference(avatar_split_clause,[],[f889,f1632,f1756])).

fof(f889,plain,
    ( r2_relset_1(sK0,sK0,k1_relat_1(k1_xboole_0),sK2)
    | r2_hidden(sK4(sK0,k1_relat_1(k1_xboole_0),sK2),sK0) ),
    inference(resolution,[],[f281,f181])).

fof(f1604,plain,
    ( spl5_67
    | spl5_56 ),
    inference(avatar_split_clause,[],[f1061,f1539,f1601])).

fof(f1061,plain,
    ( r2_relset_1(sK0,sK0,k2_funct_1(sK2),k1_xboole_0)
    | r2_hidden(sK4(sK0,k2_funct_1(sK2),k1_xboole_0),sK0) ),
    inference(resolution,[],[f283,f297])).

fof(f283,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
      | r2_relset_1(X4,X4,X5,k1_xboole_0)
      | r2_hidden(sK4(X4,X5,k1_xboole_0),X4) ) ),
    inference(resolution,[],[f89,f81])).

fof(f956,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f955])).

fof(f955,plain,
    ( $false
    | spl5_9 ),
    inference(subsumption_resolution,[],[f954,f71])).

fof(f954,plain,
    ( ~ v1_funct_1(sK1)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f945,f231])).

fof(f231,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl5_9
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f945,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f317,f74])).

fof(f317,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f312,f75])).

fof(f312,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f113,f78])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f479,plain,
    ( spl5_25
    | spl5_13 ),
    inference(avatar_split_clause,[],[f475,f340,f477])).

fof(f475,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2))
      | sK0 = k2_relset_1(X2,sK0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
      | ~ v1_funct_2(X3,X2,sK0)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f474,f75])).

fof(f474,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2))
      | sK0 = k2_relset_1(X2,sK0,X3)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
      | ~ v1_funct_2(X3,X2,sK0)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f473,f76])).

fof(f473,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2))
      | sK0 = k2_relset_1(X2,sK0,X3)
      | ~ v1_funct_2(sK2,sK0,sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
      | ~ v1_funct_2(X3,X2,sK0)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f386,f191])).

fof(f386,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | ~ v2_funct_1(sK2)
      | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2))
      | sK0 = k2_relset_1(X2,sK0,X3)
      | ~ v1_funct_2(sK2,sK0,sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
      | ~ v1_funct_2(X3,X2,sK0)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f109,f78])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | ~ v2_funct_1(X4)
      | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
      | k2_relset_1(X0,X1,X3) = X1
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k2_relset_1(X0,X1,X3) = X1
          | k1_xboole_0 = X2
          | ~ v2_funct_1(X4)
          | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k2_relset_1(X0,X1,X3) = X1
          | k1_xboole_0 = X2
          | ~ v2_funct_1(X4)
          | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f449,plain,
    ( spl5_20
    | spl5_4 ),
    inference(avatar_split_clause,[],[f151,f136,f447])).

fof(f136,plain,
    ( spl5_4
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f151,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X4)
      | ~ r2_hidden(X5,k1_xboole_0) ) ),
    inference(resolution,[],[f108,f81])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f423,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl5_4 ),
    inference(resolution,[],[f137,f87])).

fof(f87,plain,(
    ! [X0] : v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(X0))
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f137,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f373,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl5_15 ),
    inference(subsumption_resolution,[],[f371,f75])).

fof(f371,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f370,f76])).

fof(f370,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f369,f78])).

fof(f369,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f368,f71])).

fof(f368,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f367,f72])).

fof(f367,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f366,f74])).

fof(f366,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f365,f354])).

fof(f354,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK2)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl5_15
  <=> sK0 = k2_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f365,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f105,f79])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f355,plain,
    ( spl5_14
    | ~ spl5_15
    | spl5_13 ),
    inference(avatar_split_clause,[],[f346,f340,f352,f348])).

fof(f346,plain,
    ( k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f345,f75])).

fof(f345,plain,
    ( k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f344,f76])).

fof(f344,plain,
    ( k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f324,f191])).

fof(f324,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f103,f78])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f236,plain,
    ( ~ spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f227,f233,f229])).

fof(f227,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f226,f82])).

fof(f226,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f110,f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (17123)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (17122)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (17118)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (17141)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (17120)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (17128)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (17133)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (17140)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (17136)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (17139)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (17124)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (17130)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (17126)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (17132)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (17138)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (17134)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (17117)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (17121)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (17129)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (17142)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % (17125)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (17143)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.56  % (17135)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.57  % (17119)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.59  % (17137)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.77/0.60  % (17127)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 3.94/0.86  % (17127)Refutation found. Thanks to Tanya!
% 3.94/0.86  % SZS status Theorem for theBenchmark
% 3.94/0.86  % SZS output start Proof for theBenchmark
% 3.94/0.86  fof(f4143,plain,(
% 3.94/0.86    $false),
% 3.94/0.86    inference(avatar_sat_refutation,[],[f236,f355,f373,f423,f449,f479,f956,f1604,f1759,f1779,f1823,f1897,f1932,f2656,f2980,f3184,f3190,f3458,f3468,f3478,f4142])).
% 3.94/0.86  fof(f4142,plain,(
% 3.94/0.86    ~spl5_13 | ~spl5_57 | ~spl5_96 | ~spl5_119),
% 3.94/0.86    inference(avatar_contradiction_clause,[],[f4141])).
% 3.94/0.86  fof(f4141,plain,(
% 3.94/0.86    $false | (~spl5_13 | ~spl5_57 | ~spl5_96 | ~spl5_119)),
% 3.94/0.86    inference(subsumption_resolution,[],[f4140,f3140])).
% 3.94/0.86  fof(f3140,plain,(
% 3.94/0.86    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl5_13 | ~spl5_57)),
% 3.94/0.86    inference(forward_demodulation,[],[f1548,f342])).
% 3.94/0.86  fof(f342,plain,(
% 3.94/0.86    k1_xboole_0 = sK0 | ~spl5_13),
% 3.94/0.86    inference(avatar_component_clause,[],[f340])).
% 3.94/0.86  fof(f340,plain,(
% 3.94/0.86    spl5_13 <=> k1_xboole_0 = sK0),
% 3.94/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.94/0.86  fof(f1548,plain,(
% 3.94/0.86    r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | ~spl5_57),
% 3.94/0.86    inference(avatar_component_clause,[],[f1546])).
% 3.94/0.86  fof(f1546,plain,(
% 3.94/0.86    spl5_57 <=> r2_relset_1(sK0,sK0,sK2,k1_xboole_0)),
% 3.94/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 3.94/0.86  fof(f4140,plain,(
% 3.94/0.86    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl5_13 | ~spl5_57 | ~spl5_96 | ~spl5_119)),
% 3.94/0.86    inference(forward_demodulation,[],[f4139,f3857])).
% 3.94/0.86  fof(f3857,plain,(
% 3.94/0.86    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl5_13 | ~spl5_57 | ~spl5_96 | ~spl5_119)),
% 3.94/0.86    inference(forward_demodulation,[],[f3856,f3758])).
% 3.94/0.86  fof(f3758,plain,(
% 3.94/0.86    k1_xboole_0 = sK1 | (~spl5_13 | ~spl5_57 | ~spl5_96)),
% 3.94/0.86    inference(forward_demodulation,[],[f3757,f3663])).
% 3.94/0.86  fof(f3663,plain,(
% 3.94/0.86    k1_xboole_0 = sK2 | (~spl5_13 | ~spl5_57)),
% 3.94/0.86    inference(subsumption_resolution,[],[f3662,f3362])).
% 3.94/0.86  fof(f3362,plain,(
% 3.94/0.86    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_13),
% 3.94/0.86    inference(superposition,[],[f78,f342])).
% 3.94/0.86  fof(f78,plain,(
% 3.94/0.86    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.86    inference(cnf_transformation,[],[f65])).
% 3.94/0.86  fof(f65,plain,(
% 3.94/0.86    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.94/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f64,f63])).
% 3.94/0.86  fof(f63,plain,(
% 3.94/0.86    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.94/0.86    introduced(choice_axiom,[])).
% 3.94/0.86  fof(f64,plain,(
% 3.94/0.86    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 3.94/0.86    introduced(choice_axiom,[])).
% 3.94/0.86  fof(f29,plain,(
% 3.94/0.86    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.94/0.86    inference(flattening,[],[f28])).
% 3.94/0.86  fof(f28,plain,(
% 3.94/0.86    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.94/0.86    inference(ennf_transformation,[],[f25])).
% 3.94/0.86  fof(f25,negated_conjecture,(
% 3.94/0.86    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.94/0.86    inference(negated_conjecture,[],[f24])).
% 3.94/0.86  fof(f24,conjecture,(
% 3.94/0.86    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.94/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 3.94/0.86  fof(f3662,plain,(
% 3.94/0.86    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_13 | ~spl5_57)),
% 3.94/0.86    inference(subsumption_resolution,[],[f3661,f81])).
% 3.94/0.86  fof(f81,plain,(
% 3.94/0.86    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.94/0.86    inference(cnf_transformation,[],[f3])).
% 3.94/0.86  fof(f3,axiom,(
% 3.94/0.86    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.94/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.94/0.86  fof(f3661,plain,(
% 3.94/0.86    k1_xboole_0 = sK2 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_13 | ~spl5_57)),
% 3.94/0.86    inference(resolution,[],[f3140,f110])).
% 3.94/0.86  fof(f110,plain,(
% 3.94/0.86    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.94/0.86    inference(cnf_transformation,[],[f70])).
% 3.94/0.86  fof(f70,plain,(
% 3.94/0.86    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.86    inference(nnf_transformation,[],[f60])).
% 3.94/0.86  fof(f60,plain,(
% 3.94/0.86    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.86    inference(flattening,[],[f59])).
% 3.94/0.86  fof(f59,plain,(
% 3.94/0.86    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.94/0.86    inference(ennf_transformation,[],[f12])).
% 3.94/0.87  fof(f12,axiom,(
% 3.94/0.87    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 3.94/0.87  fof(f3757,plain,(
% 3.94/0.87    sK1 = sK2 | (~spl5_13 | ~spl5_96)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3756,f3362])).
% 3.94/0.87  fof(f3756,plain,(
% 3.94/0.87    sK1 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_13 | ~spl5_96)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3754,f3359])).
% 3.94/0.87  fof(f3359,plain,(
% 3.94/0.87    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_13),
% 3.94/0.87    inference(superposition,[],[f74,f342])).
% 3.94/0.87  fof(f74,plain,(
% 3.94/0.87    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f3754,plain,(
% 3.94/0.87    sK1 = sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_13 | ~spl5_96)),
% 3.94/0.87    inference(resolution,[],[f3315,f110])).
% 3.94/0.87  fof(f3315,plain,(
% 3.94/0.87    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK1) | (~spl5_13 | ~spl5_96)),
% 3.94/0.87    inference(forward_demodulation,[],[f1741,f342])).
% 3.94/0.87  fof(f1741,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,sK2,sK1) | ~spl5_96),
% 3.94/0.87    inference(avatar_component_clause,[],[f1739])).
% 3.94/0.87  fof(f1739,plain,(
% 3.94/0.87    spl5_96 <=> r2_relset_1(sK0,sK0,sK2,sK1)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 3.94/0.87  fof(f3856,plain,(
% 3.94/0.87    sK1 = k2_funct_1(sK1) | (~spl5_13 | ~spl5_119)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3855,f3388])).
% 3.94/0.87  fof(f3388,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_13),
% 3.94/0.87    inference(superposition,[],[f293,f342])).
% 3.94/0.87  fof(f293,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.87    inference(forward_demodulation,[],[f292,f250])).
% 3.94/0.87  fof(f250,plain,(
% 3.94/0.87    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 3.94/0.87    inference(subsumption_resolution,[],[f249,f71])).
% 3.94/0.87  fof(f71,plain,(
% 3.94/0.87    v1_funct_1(sK1)),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f249,plain,(
% 3.94/0.87    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(subsumption_resolution,[],[f248,f72])).
% 3.94/0.87  fof(f72,plain,(
% 3.94/0.87    v1_funct_2(sK1,sK0,sK0)),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f248,plain,(
% 3.94/0.87    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(subsumption_resolution,[],[f243,f73])).
% 3.94/0.87  fof(f73,plain,(
% 3.94/0.87    v3_funct_2(sK1,sK0,sK0)),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f243,plain,(
% 3.94/0.87    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(resolution,[],[f91,f74])).
% 3.94/0.87  fof(f91,plain,(
% 3.94/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f37])).
% 3.94/0.87  fof(f37,plain,(
% 3.94/0.87    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.94/0.87    inference(flattening,[],[f36])).
% 3.94/0.87  fof(f36,plain,(
% 3.94/0.87    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.94/0.87    inference(ennf_transformation,[],[f18])).
% 3.94/0.87  fof(f18,axiom,(
% 3.94/0.87    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 3.94/0.87  fof(f292,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.87    inference(subsumption_resolution,[],[f291,f71])).
% 3.94/0.87  fof(f291,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(subsumption_resolution,[],[f290,f72])).
% 3.94/0.87  fof(f290,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(subsumption_resolution,[],[f285,f73])).
% 3.94/0.87  fof(f285,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(resolution,[],[f95,f74])).
% 3.94/0.87  fof(f95,plain,(
% 3.94/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f39])).
% 3.94/0.87  fof(f39,plain,(
% 3.94/0.87    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.94/0.87    inference(flattening,[],[f38])).
% 3.94/0.87  fof(f38,plain,(
% 3.94/0.87    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.94/0.87    inference(ennf_transformation,[],[f16])).
% 3.94/0.87  fof(f16,axiom,(
% 3.94/0.87    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 3.94/0.87  fof(f3855,plain,(
% 3.94/0.87    sK1 = k2_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_13 | ~spl5_119)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3853,f3359])).
% 3.94/0.87  fof(f3853,plain,(
% 3.94/0.87    sK1 = k2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_13 | ~spl5_119)),
% 3.94/0.87    inference(resolution,[],[f3307,f110])).
% 3.94/0.87  fof(f3307,plain,(
% 3.94/0.87    r2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK1),sK1) | (~spl5_13 | ~spl5_119)),
% 3.94/0.87    inference(forward_demodulation,[],[f1931,f342])).
% 3.94/0.87  fof(f1931,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k2_funct_1(sK1),sK1) | ~spl5_119),
% 3.94/0.87    inference(avatar_component_clause,[],[f1929])).
% 3.94/0.87  fof(f1929,plain,(
% 3.94/0.87    spl5_119 <=> r2_relset_1(sK0,sK0,k2_funct_1(sK1),sK1)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).
% 3.94/0.87  fof(f4139,plain,(
% 3.94/0.87    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) | (~spl5_13 | ~spl5_57 | ~spl5_96)),
% 3.94/0.87    inference(forward_demodulation,[],[f4136,f3739])).
% 3.94/0.87  fof(f3739,plain,(
% 3.94/0.87    k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) | (~spl5_13 | ~spl5_57)),
% 3.94/0.87    inference(forward_demodulation,[],[f3705,f342])).
% 3.94/0.87  fof(f3705,plain,(
% 3.94/0.87    k2_funct_1(k1_xboole_0) = k2_funct_2(sK0,k1_xboole_0) | (~spl5_13 | ~spl5_57)),
% 3.94/0.87    inference(superposition,[],[f253,f3663])).
% 3.94/0.87  fof(f253,plain,(
% 3.94/0.87    k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f252,f75])).
% 3.94/0.87  fof(f75,plain,(
% 3.94/0.87    v1_funct_1(sK2)),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f252,plain,(
% 3.94/0.87    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f251,f76])).
% 3.94/0.87  fof(f76,plain,(
% 3.94/0.87    v1_funct_2(sK2,sK0,sK0)),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f251,plain,(
% 3.94/0.87    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f244,f77])).
% 3.94/0.87  fof(f77,plain,(
% 3.94/0.87    v3_funct_2(sK2,sK0,sK0)),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f244,plain,(
% 3.94/0.87    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f91,f78])).
% 3.94/0.87  fof(f4136,plain,(
% 3.94/0.87    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl5_13 | ~spl5_57 | ~spl5_96)),
% 3.94/0.87    inference(superposition,[],[f3364,f3758])).
% 3.94/0.87  fof(f3364,plain,(
% 3.94/0.87    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_2(k1_xboole_0,sK1)) | ~spl5_13),
% 3.94/0.87    inference(superposition,[],[f80,f342])).
% 3.94/0.87  fof(f80,plain,(
% 3.94/0.87    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f3478,plain,(
% 3.94/0.87    ~spl5_13 | ~spl5_20 | ~spl5_118),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f3477])).
% 3.94/0.87  fof(f3477,plain,(
% 3.94/0.87    $false | (~spl5_13 | ~spl5_20 | ~spl5_118)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3422,f448])).
% 3.94/0.87  fof(f448,plain,(
% 3.94/0.87    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) ) | ~spl5_20),
% 3.94/0.87    inference(avatar_component_clause,[],[f447])).
% 3.94/0.87  fof(f447,plain,(
% 3.94/0.87    spl5_20 <=> ! [X5] : ~r2_hidden(X5,k1_xboole_0)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 3.94/0.87  fof(f3422,plain,(
% 3.94/0.87    r2_hidden(sK4(k1_xboole_0,k2_funct_1(sK1),sK1),k1_xboole_0) | (~spl5_13 | ~spl5_118)),
% 3.94/0.87    inference(superposition,[],[f1927,f342])).
% 3.94/0.87  fof(f1927,plain,(
% 3.94/0.87    r2_hidden(sK4(sK0,k2_funct_1(sK1),sK1),sK0) | ~spl5_118),
% 3.94/0.87    inference(avatar_component_clause,[],[f1925])).
% 3.94/0.87  fof(f1925,plain,(
% 3.94/0.87    spl5_118 <=> r2_hidden(sK4(sK0,k2_funct_1(sK1),sK1),sK0)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 3.94/0.87  fof(f3468,plain,(
% 3.94/0.87    ~spl5_13 | ~spl5_20 | ~spl5_111),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f3467])).
% 3.94/0.87  fof(f3467,plain,(
% 3.94/0.87    $false | (~spl5_13 | ~spl5_20 | ~spl5_111)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3416,f448])).
% 3.94/0.87  fof(f3416,plain,(
% 3.94/0.87    r2_hidden(sK4(k1_xboole_0,sK2,sK1),k1_xboole_0) | (~spl5_13 | ~spl5_111)),
% 3.94/0.87    inference(superposition,[],[f1821,f342])).
% 3.94/0.87  fof(f1821,plain,(
% 3.94/0.87    r2_hidden(sK4(sK0,sK2,sK1),sK0) | ~spl5_111),
% 3.94/0.87    inference(avatar_component_clause,[],[f1819])).
% 3.94/0.87  fof(f1819,plain,(
% 3.94/0.87    spl5_111 <=> r2_hidden(sK4(sK0,sK2,sK1),sK0)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).
% 3.94/0.87  fof(f3458,plain,(
% 3.94/0.87    ~spl5_13 | ~spl5_20 | ~spl5_99),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f3457])).
% 3.94/0.87  fof(f3457,plain,(
% 3.94/0.87    $false | (~spl5_13 | ~spl5_20 | ~spl5_99)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3411,f448])).
% 3.94/0.87  fof(f3411,plain,(
% 3.94/0.87    r2_hidden(sK4(k1_xboole_0,k1_relat_1(k1_xboole_0),sK2),k1_xboole_0) | (~spl5_13 | ~spl5_99)),
% 3.94/0.87    inference(superposition,[],[f1758,f342])).
% 3.94/0.87  fof(f1758,plain,(
% 3.94/0.87    r2_hidden(sK4(sK0,k1_relat_1(k1_xboole_0),sK2),sK0) | ~spl5_99),
% 3.94/0.87    inference(avatar_component_clause,[],[f1756])).
% 3.94/0.87  fof(f1756,plain,(
% 3.94/0.87    spl5_99 <=> r2_hidden(sK4(sK0,k1_relat_1(k1_xboole_0),sK2),sK0)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).
% 3.94/0.87  fof(f3190,plain,(
% 3.94/0.87    ~spl5_13 | ~spl5_20 | ~spl5_67),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f3189])).
% 3.94/0.87  fof(f3189,plain,(
% 3.94/0.87    $false | (~spl5_13 | ~spl5_20 | ~spl5_67)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3188,f448])).
% 3.94/0.87  fof(f3188,plain,(
% 3.94/0.87    r2_hidden(sK4(k1_xboole_0,k2_funct_1(sK2),k1_xboole_0),k1_xboole_0) | (~spl5_13 | ~spl5_67)),
% 3.94/0.87    inference(forward_demodulation,[],[f1603,f342])).
% 3.94/0.87  fof(f1603,plain,(
% 3.94/0.87    r2_hidden(sK4(sK0,k2_funct_1(sK2),k1_xboole_0),sK0) | ~spl5_67),
% 3.94/0.87    inference(avatar_component_clause,[],[f1601])).
% 3.94/0.87  fof(f1601,plain,(
% 3.94/0.87    spl5_67 <=> r2_hidden(sK4(sK0,k2_funct_1(sK2),k1_xboole_0),sK0)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 3.94/0.87  fof(f3184,plain,(
% 3.94/0.87    ~spl5_13 | ~spl5_20 | ~spl5_103),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f3183])).
% 3.94/0.87  fof(f3183,plain,(
% 3.94/0.87    $false | (~spl5_13 | ~spl5_20 | ~spl5_103)),
% 3.94/0.87    inference(subsumption_resolution,[],[f3182,f448])).
% 3.94/0.87  fof(f3182,plain,(
% 3.94/0.87    r2_hidden(sK4(k1_xboole_0,k2_funct_1(sK2),sK2),k1_xboole_0) | (~spl5_13 | ~spl5_103)),
% 3.94/0.87    inference(forward_demodulation,[],[f1778,f342])).
% 3.94/0.87  fof(f1778,plain,(
% 3.94/0.87    r2_hidden(sK4(sK0,k2_funct_1(sK2),sK2),sK0) | ~spl5_103),
% 3.94/0.87    inference(avatar_component_clause,[],[f1776])).
% 3.94/0.87  fof(f1776,plain,(
% 3.94/0.87    spl5_103 <=> r2_hidden(sK4(sK0,k2_funct_1(sK2),sK2),sK0)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).
% 3.94/0.87  fof(f2980,plain,(
% 3.94/0.87    ~spl5_10 | spl5_12 | spl5_13 | ~spl5_14 | ~spl5_25),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f2979])).
% 3.94/0.87  fof(f2979,plain,(
% 3.94/0.87    $false | (~spl5_10 | spl5_12 | spl5_13 | ~spl5_14 | ~spl5_25)),
% 3.94/0.87    inference(subsumption_resolution,[],[f2978,f2961])).
% 3.94/0.87  fof(f2961,plain,(
% 3.94/0.87    sK0 != k2_relat_1(k6_partfun1(sK0)) | (~spl5_10 | spl5_12 | spl5_13 | ~spl5_25)),
% 3.94/0.87    inference(superposition,[],[f2184,f170])).
% 3.94/0.87  fof(f170,plain,(
% 3.94/0.87    ( ! [X0] : (k2_relset_1(X0,X0,k6_partfun1(X0)) = k2_relat_1(k6_partfun1(X0))) )),
% 3.94/0.87    inference(resolution,[],[f99,f82])).
% 3.94/0.87  fof(f82,plain,(
% 3.94/0.87    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.94/0.87    inference(cnf_transformation,[],[f26])).
% 3.94/0.87  fof(f26,plain,(
% 3.94/0.87    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.94/0.87    inference(pure_predicate_removal,[],[f17])).
% 3.94/0.87  fof(f17,axiom,(
% 3.94/0.87    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 3.94/0.87  fof(f99,plain,(
% 3.94/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f44])).
% 3.94/0.87  fof(f44,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.87    inference(ennf_transformation,[],[f11])).
% 3.94/0.87  fof(f11,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 3.94/0.87  fof(f2184,plain,(
% 3.94/0.87    sK0 != k2_relset_1(sK0,sK0,k6_partfun1(sK0)) | (~spl5_10 | spl5_12 | spl5_13 | ~spl5_25)),
% 3.94/0.87    inference(forward_demodulation,[],[f2183,f235])).
% 3.94/0.87  fof(f235,plain,(
% 3.94/0.87    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) | ~spl5_10),
% 3.94/0.87    inference(avatar_component_clause,[],[f233])).
% 3.94/0.87  fof(f233,plain,(
% 3.94/0.87    spl5_10 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.94/0.87  fof(f2183,plain,(
% 3.94/0.87    sK0 != k2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)) | (spl5_12 | spl5_13 | ~spl5_25)),
% 3.94/0.87    inference(subsumption_resolution,[],[f2182,f2001])).
% 3.94/0.87  fof(f2001,plain,(
% 3.94/0.87    sK0 != k2_relset_1(sK0,sK0,sK1) | (spl5_12 | spl5_13)),
% 3.94/0.87    inference(global_subsumption,[],[f338])).
% 3.94/0.87  fof(f338,plain,(
% 3.94/0.87    sK0 != k2_relset_1(sK0,sK0,sK1) | spl5_12),
% 3.94/0.87    inference(avatar_component_clause,[],[f336])).
% 3.94/0.87  fof(f336,plain,(
% 3.94/0.87    spl5_12 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.94/0.87  fof(f2182,plain,(
% 3.94/0.87    sK0 != k2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl5_25),
% 3.94/0.87    inference(subsumption_resolution,[],[f2181,f72])).
% 3.94/0.87  fof(f2181,plain,(
% 3.94/0.87    ~v1_funct_2(sK1,sK0,sK0) | sK0 != k2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl5_25),
% 3.94/0.87    inference(subsumption_resolution,[],[f2163,f71])).
% 3.94/0.87  fof(f2163,plain,(
% 3.94/0.87    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | sK0 != k2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)) | sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl5_25),
% 3.94/0.87    inference(resolution,[],[f478,f74])).
% 3.94/0.87  fof(f478,plain,(
% 3.94/0.87    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,sK0) | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2)) | sK0 = k2_relset_1(X2,sK0,X3)) ) | ~spl5_25),
% 3.94/0.87    inference(avatar_component_clause,[],[f477])).
% 3.94/0.87  fof(f477,plain,(
% 3.94/0.87    spl5_25 <=> ! [X3,X2] : (sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | sK0 = k2_relset_1(X2,sK0,X3))),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 3.94/0.87  fof(f2978,plain,(
% 3.94/0.87    sK0 = k2_relat_1(k6_partfun1(sK0)) | ~spl5_14),
% 3.94/0.87    inference(forward_demodulation,[],[f2973,f529])).
% 3.94/0.87  fof(f529,plain,(
% 3.94/0.87    sK0 = k1_relat_1(sK2)),
% 3.94/0.87    inference(superposition,[],[f212,f164])).
% 3.94/0.87  fof(f164,plain,(
% 3.94/0.87    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f98,f78])).
% 3.94/0.87  fof(f98,plain,(
% 3.94/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f43])).
% 3.94/0.87  fof(f43,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.87    inference(ennf_transformation,[],[f10])).
% 3.94/0.87  fof(f10,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.94/0.87  fof(f212,plain,(
% 3.94/0.87    sK0 = k1_relset_1(sK0,sK0,sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f211,f75])).
% 3.94/0.87  fof(f211,plain,(
% 3.94/0.87    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f205,f76])).
% 3.94/0.87  fof(f205,plain,(
% 3.94/0.87    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f96,f78])).
% 3.94/0.87  fof(f96,plain,(
% 3.94/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f41])).
% 3.94/0.87  fof(f41,plain,(
% 3.94/0.87    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.94/0.87    inference(flattening,[],[f40])).
% 3.94/0.87  fof(f40,plain,(
% 3.94/0.87    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.94/0.87    inference(ennf_transformation,[],[f23])).
% 3.94/0.87  fof(f23,axiom,(
% 3.94/0.87    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 3.94/0.87  fof(f2973,plain,(
% 3.94/0.87    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl5_14),
% 3.94/0.87    inference(superposition,[],[f301,f350])).
% 3.94/0.87  fof(f350,plain,(
% 3.94/0.87    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl5_14),
% 3.94/0.87    inference(avatar_component_clause,[],[f348])).
% 3.94/0.87  fof(f348,plain,(
% 3.94/0.87    spl5_14 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 3.94/0.87  fof(f301,plain,(
% 3.94/0.87    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 3.94/0.87    inference(subsumption_resolution,[],[f300,f144])).
% 3.94/0.87  fof(f144,plain,(
% 3.94/0.87    v1_relat_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f97,f78])).
% 3.94/0.87  fof(f97,plain,(
% 3.94/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f42])).
% 3.94/0.87  fof(f42,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.87    inference(ennf_transformation,[],[f8])).
% 3.94/0.87  fof(f8,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.94/0.87  fof(f300,plain,(
% 3.94/0.87    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f298,f75])).
% 3.94/0.87  fof(f298,plain,(
% 3.94/0.87    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f191,f85])).
% 3.94/0.87  fof(f85,plain,(
% 3.94/0.87    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f32])).
% 3.94/0.87  fof(f32,plain,(
% 3.94/0.87    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.94/0.87    inference(flattening,[],[f31])).
% 3.94/0.87  fof(f31,plain,(
% 3.94/0.87    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.94/0.87    inference(ennf_transformation,[],[f7])).
% 3.94/0.87  fof(f7,axiom,(
% 3.94/0.87    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 3.94/0.87  fof(f191,plain,(
% 3.94/0.87    v2_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f190,f75])).
% 3.94/0.87  fof(f190,plain,(
% 3.94/0.87    ~v1_funct_1(sK2) | v2_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f184,f77])).
% 3.94/0.87  fof(f184,plain,(
% 3.94/0.87    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f102,f78])).
% 3.94/0.87  fof(f102,plain,(
% 3.94/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f47])).
% 3.94/0.87  fof(f47,plain,(
% 3.94/0.87    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.87    inference(flattening,[],[f46])).
% 3.94/0.87  fof(f46,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.87    inference(ennf_transformation,[],[f27])).
% 3.94/0.87  fof(f27,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.94/0.87    inference(pure_predicate_removal,[],[f14])).
% 3.94/0.87  fof(f14,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 3.94/0.87  fof(f2656,plain,(
% 3.94/0.87    ~spl5_56 | spl5_57 | ~spl5_73 | ~spl5_81),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f2655])).
% 3.94/0.87  fof(f2655,plain,(
% 3.94/0.87    $false | (~spl5_56 | spl5_57 | ~spl5_73 | ~spl5_81)),
% 3.94/0.87    inference(subsumption_resolution,[],[f2654,f1547])).
% 3.94/0.87  fof(f1547,plain,(
% 3.94/0.87    ~r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | spl5_57),
% 3.94/0.87    inference(avatar_component_clause,[],[f1546])).
% 3.94/0.87  fof(f2654,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,sK2,k1_xboole_0) | (~spl5_56 | ~spl5_73 | ~spl5_81)),
% 3.94/0.87    inference(forward_demodulation,[],[f2624,f2484])).
% 3.94/0.87  fof(f2484,plain,(
% 3.94/0.87    sK2 = k1_relat_1(k1_xboole_0) | ~spl5_73),
% 3.94/0.87    inference(subsumption_resolution,[],[f2483,f181])).
% 3.94/0.87  fof(f181,plain,(
% 3.94/0.87    ( ! [X1] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1))) )),
% 3.94/0.87    inference(forward_demodulation,[],[f176,f166])).
% 3.94/0.87  fof(f166,plain,(
% 3.94/0.87    ( ! [X2,X1] : (k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 3.94/0.87    inference(resolution,[],[f98,f81])).
% 3.94/0.87  fof(f176,plain,(
% 3.94/0.87    ( ! [X2,X1] : (m1_subset_1(k1_relset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X1))) )),
% 3.94/0.87    inference(resolution,[],[f100,f81])).
% 3.94/0.87  fof(f100,plain,(
% 3.94/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 3.94/0.87    inference(cnf_transformation,[],[f45])).
% 3.94/0.87  fof(f45,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.87    inference(ennf_transformation,[],[f9])).
% 3.94/0.87  fof(f9,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 3.94/0.87  fof(f2483,plain,(
% 3.94/0.87    sK2 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_73),
% 3.94/0.87    inference(subsumption_resolution,[],[f2482,f78])).
% 3.94/0.87  fof(f2482,plain,(
% 3.94/0.87    sK2 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_73),
% 3.94/0.87    inference(resolution,[],[f1634,f110])).
% 3.94/0.87  fof(f1634,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k1_relat_1(k1_xboole_0),sK2) | ~spl5_73),
% 3.94/0.87    inference(avatar_component_clause,[],[f1632])).
% 3.94/0.87  fof(f1632,plain,(
% 3.94/0.87    spl5_73 <=> r2_relset_1(sK0,sK0,k1_relat_1(k1_xboole_0),sK2)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 3.94/0.87  fof(f2624,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl5_56 | ~spl5_73 | ~spl5_81)),
% 3.94/0.87    inference(superposition,[],[f1634,f2492])).
% 3.94/0.87  fof(f2492,plain,(
% 3.94/0.87    k1_xboole_0 = sK2 | (~spl5_56 | ~spl5_81)),
% 3.94/0.87    inference(forward_demodulation,[],[f2491,f2412])).
% 3.94/0.87  fof(f2412,plain,(
% 3.94/0.87    k1_xboole_0 = k2_funct_1(sK2) | ~spl5_56),
% 3.94/0.87    inference(subsumption_resolution,[],[f2411,f297])).
% 3.94/0.87  fof(f297,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.87    inference(forward_demodulation,[],[f296,f253])).
% 3.94/0.87  fof(f296,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.87    inference(subsumption_resolution,[],[f295,f75])).
% 3.94/0.87  fof(f295,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f294,f76])).
% 3.94/0.87  fof(f294,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f286,f77])).
% 3.94/0.87  fof(f286,plain,(
% 3.94/0.87    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f95,f78])).
% 3.94/0.87  fof(f2411,plain,(
% 3.94/0.87    k1_xboole_0 = k2_funct_1(sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_56),
% 3.94/0.87    inference(subsumption_resolution,[],[f2410,f81])).
% 3.94/0.87  fof(f2410,plain,(
% 3.94/0.87    k1_xboole_0 = k2_funct_1(sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_56),
% 3.94/0.87    inference(resolution,[],[f1541,f110])).
% 3.94/0.87  fof(f1541,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k2_funct_1(sK2),k1_xboole_0) | ~spl5_56),
% 3.94/0.87    inference(avatar_component_clause,[],[f1539])).
% 3.94/0.87  fof(f1539,plain,(
% 3.94/0.87    spl5_56 <=> r2_relset_1(sK0,sK0,k2_funct_1(sK2),k1_xboole_0)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 3.94/0.87  fof(f2491,plain,(
% 3.94/0.87    sK2 = k2_funct_1(sK2) | ~spl5_81),
% 3.94/0.87    inference(subsumption_resolution,[],[f2490,f297])).
% 3.94/0.87  fof(f2490,plain,(
% 3.94/0.87    sK2 = k2_funct_1(sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_81),
% 3.94/0.87    inference(subsumption_resolution,[],[f2489,f78])).
% 3.94/0.87  fof(f2489,plain,(
% 3.94/0.87    sK2 = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_81),
% 3.94/0.87    inference(resolution,[],[f1670,f110])).
% 3.94/0.87  fof(f1670,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k2_funct_1(sK2),sK2) | ~spl5_81),
% 3.94/0.87    inference(avatar_component_clause,[],[f1668])).
% 3.94/0.87  fof(f1668,plain,(
% 3.94/0.87    spl5_81 <=> r2_relset_1(sK0,sK0,k2_funct_1(sK2),sK2)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 3.94/0.87  fof(f1932,plain,(
% 3.94/0.87    spl5_118 | spl5_119),
% 3.94/0.87    inference(avatar_split_clause,[],[f849,f1929,f1925])).
% 3.94/0.87  fof(f849,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k2_funct_1(sK1),sK1) | r2_hidden(sK4(sK0,k2_funct_1(sK1),sK1),sK0)),
% 3.94/0.87    inference(resolution,[],[f280,f293])).
% 3.94/0.87  fof(f280,plain,(
% 3.94/0.87    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,X0,sK1) | r2_hidden(sK4(sK0,X0,sK1),sK0)) )),
% 3.94/0.87    inference(resolution,[],[f89,f74])).
% 3.94/0.87  fof(f89,plain,(
% 3.94/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | r2_hidden(sK4(X0,X1,X2),X0) | r2_relset_1(X0,X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.94/0.87    inference(cnf_transformation,[],[f69])).
% 3.94/0.87  fof(f69,plain,(
% 3.94/0.87    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.94/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f68])).
% 3.94/0.87  fof(f68,plain,(
% 3.94/0.87    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK4(X0,X1,X2)) != k11_relat_1(X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 3.94/0.87    introduced(choice_axiom,[])).
% 3.94/0.87  fof(f35,plain,(
% 3.94/0.87    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.94/0.87    inference(flattening,[],[f34])).
% 3.94/0.87  fof(f34,plain,(
% 3.94/0.87    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.94/0.87    inference(ennf_transformation,[],[f13])).
% 3.94/0.87  fof(f13,axiom,(
% 3.94/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).
% 3.94/0.87  fof(f1897,plain,(
% 3.94/0.87    ~spl5_12 | spl5_13),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f1896])).
% 3.94/0.87  fof(f1896,plain,(
% 3.94/0.87    $false | (~spl5_12 | spl5_13)),
% 3.94/0.87    inference(subsumption_resolution,[],[f1895,f159])).
% 3.94/0.87  fof(f159,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,sK2,sK2)),
% 3.94/0.87    inference(resolution,[],[f115,f78])).
% 3.94/0.87  fof(f115,plain,(
% 3.94/0.87    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 3.94/0.87    inference(duplicate_literal_removal,[],[f114])).
% 3.94/0.87  fof(f114,plain,(
% 3.94/0.87    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.94/0.87    inference(equality_resolution,[],[f111])).
% 3.94/0.87  fof(f111,plain,(
% 3.94/0.87    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.94/0.87    inference(cnf_transformation,[],[f70])).
% 3.94/0.87  fof(f1895,plain,(
% 3.94/0.87    ~r2_relset_1(sK0,sK0,sK2,sK2) | (~spl5_12 | spl5_13)),
% 3.94/0.87    inference(forward_demodulation,[],[f515,f1473])).
% 3.94/0.87  fof(f1473,plain,(
% 3.94/0.87    sK2 = k2_funct_1(sK1) | (~spl5_12 | spl5_13)),
% 3.94/0.87    inference(global_subsumption,[],[f341,f1472])).
% 3.94/0.87  fof(f1472,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~spl5_12),
% 3.94/0.87    inference(subsumption_resolution,[],[f1471,f71])).
% 3.94/0.87  fof(f1471,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1) | ~spl5_12),
% 3.94/0.87    inference(subsumption_resolution,[],[f1470,f72])).
% 3.94/0.87  fof(f1470,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl5_12),
% 3.94/0.87    inference(subsumption_resolution,[],[f1469,f74])).
% 3.94/0.87  fof(f1469,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl5_12),
% 3.94/0.87    inference(subsumption_resolution,[],[f1468,f75])).
% 3.94/0.87  fof(f1468,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl5_12),
% 3.94/0.87    inference(subsumption_resolution,[],[f1467,f76])).
% 3.94/0.87  fof(f1467,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl5_12),
% 3.94/0.87    inference(subsumption_resolution,[],[f1466,f78])).
% 3.94/0.87  fof(f1466,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl5_12),
% 3.94/0.87    inference(subsumption_resolution,[],[f1465,f337])).
% 3.94/0.87  fof(f337,plain,(
% 3.94/0.87    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl5_12),
% 3.94/0.87    inference(avatar_component_clause,[],[f336])).
% 3.94/0.87  fof(f1465,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(subsumption_resolution,[],[f391,f189])).
% 3.94/0.87  fof(f189,plain,(
% 3.94/0.87    v2_funct_1(sK1)),
% 3.94/0.87    inference(subsumption_resolution,[],[f188,f71])).
% 3.94/0.87  fof(f188,plain,(
% 3.94/0.87    ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 3.94/0.87    inference(subsumption_resolution,[],[f183,f73])).
% 3.94/0.87  fof(f183,plain,(
% 3.94/0.87    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 3.94/0.87    inference(resolution,[],[f102,f74])).
% 3.94/0.87  fof(f391,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(duplicate_literal_removal,[],[f390])).
% 3.94/0.87  fof(f390,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(resolution,[],[f106,f79])).
% 3.94/0.87  fof(f79,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.94/0.87    inference(cnf_transformation,[],[f65])).
% 3.94/0.87  fof(f106,plain,(
% 3.94/0.87    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_funct_1(X2) = X3 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f53])).
% 3.94/0.87  fof(f53,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.94/0.87    inference(flattening,[],[f52])).
% 3.94/0.87  fof(f52,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.94/0.87    inference(ennf_transformation,[],[f22])).
% 3.94/0.87  fof(f22,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 3.94/0.87  fof(f341,plain,(
% 3.94/0.87    k1_xboole_0 != sK0 | spl5_13),
% 3.94/0.87    inference(avatar_component_clause,[],[f340])).
% 3.94/0.87  fof(f515,plain,(
% 3.94/0.87    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 3.94/0.87    inference(superposition,[],[f80,f250])).
% 3.94/0.87  fof(f1823,plain,(
% 3.94/0.87    spl5_111 | spl5_96),
% 3.94/0.87    inference(avatar_split_clause,[],[f848,f1739,f1819])).
% 3.94/0.87  fof(f848,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,sK2,sK1) | r2_hidden(sK4(sK0,sK2,sK1),sK0)),
% 3.94/0.87    inference(resolution,[],[f280,f78])).
% 3.94/0.87  fof(f1779,plain,(
% 3.94/0.87    spl5_103 | spl5_81),
% 3.94/0.87    inference(avatar_split_clause,[],[f885,f1668,f1776])).
% 3.94/0.87  fof(f885,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k2_funct_1(sK2),sK2) | r2_hidden(sK4(sK0,k2_funct_1(sK2),sK2),sK0)),
% 3.94/0.87    inference(resolution,[],[f281,f297])).
% 3.94/0.87  fof(f281,plain,(
% 3.94/0.87    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,X1,sK2) | r2_hidden(sK4(sK0,X1,sK2),sK0)) )),
% 3.94/0.87    inference(resolution,[],[f89,f78])).
% 3.94/0.87  fof(f1759,plain,(
% 3.94/0.87    spl5_99 | spl5_73),
% 3.94/0.87    inference(avatar_split_clause,[],[f889,f1632,f1756])).
% 3.94/0.87  fof(f889,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k1_relat_1(k1_xboole_0),sK2) | r2_hidden(sK4(sK0,k1_relat_1(k1_xboole_0),sK2),sK0)),
% 3.94/0.87    inference(resolution,[],[f281,f181])).
% 3.94/0.87  fof(f1604,plain,(
% 3.94/0.87    spl5_67 | spl5_56),
% 3.94/0.87    inference(avatar_split_clause,[],[f1061,f1539,f1601])).
% 3.94/0.87  fof(f1061,plain,(
% 3.94/0.87    r2_relset_1(sK0,sK0,k2_funct_1(sK2),k1_xboole_0) | r2_hidden(sK4(sK0,k2_funct_1(sK2),k1_xboole_0),sK0)),
% 3.94/0.87    inference(resolution,[],[f283,f297])).
% 3.94/0.87  fof(f283,plain,(
% 3.94/0.87    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4))) | r2_relset_1(X4,X4,X5,k1_xboole_0) | r2_hidden(sK4(X4,X5,k1_xboole_0),X4)) )),
% 3.94/0.87    inference(resolution,[],[f89,f81])).
% 3.94/0.87  fof(f956,plain,(
% 3.94/0.87    spl5_9),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f955])).
% 3.94/0.87  fof(f955,plain,(
% 3.94/0.87    $false | spl5_9),
% 3.94/0.87    inference(subsumption_resolution,[],[f954,f71])).
% 3.94/0.87  fof(f954,plain,(
% 3.94/0.87    ~v1_funct_1(sK1) | spl5_9),
% 3.94/0.87    inference(subsumption_resolution,[],[f945,f231])).
% 3.94/0.87  fof(f231,plain,(
% 3.94/0.87    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_9),
% 3.94/0.87    inference(avatar_component_clause,[],[f229])).
% 3.94/0.87  fof(f229,plain,(
% 3.94/0.87    spl5_9 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.94/0.87  fof(f945,plain,(
% 3.94/0.87    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 3.94/0.87    inference(resolution,[],[f317,f74])).
% 3.94/0.87  fof(f317,plain,(
% 3.94/0.87    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(X5)) )),
% 3.94/0.87    inference(subsumption_resolution,[],[f312,f75])).
% 3.94/0.87  fof(f312,plain,(
% 3.94/0.87    ( ! [X4,X5,X3] : (m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 3.94/0.87    inference(resolution,[],[f113,f78])).
% 3.94/0.87  fof(f113,plain,(
% 3.94/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f62])).
% 3.94/0.87  fof(f62,plain,(
% 3.94/0.87    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.94/0.87    inference(flattening,[],[f61])).
% 3.94/0.87  fof(f61,plain,(
% 3.94/0.87    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.94/0.87    inference(ennf_transformation,[],[f15])).
% 3.94/0.87  fof(f15,axiom,(
% 3.94/0.87    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 3.94/0.87  fof(f479,plain,(
% 3.94/0.87    spl5_25 | spl5_13),
% 3.94/0.87    inference(avatar_split_clause,[],[f475,f340,f477])).
% 3.94/0.87  fof(f475,plain,(
% 3.94/0.87    ( ! [X2,X3] : (k1_xboole_0 = sK0 | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2)) | sK0 = k2_relset_1(X2,sK0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_2(X3,X2,sK0) | ~v1_funct_1(X3)) )),
% 3.94/0.87    inference(subsumption_resolution,[],[f474,f75])).
% 3.94/0.87  fof(f474,plain,(
% 3.94/0.87    ( ! [X2,X3] : (k1_xboole_0 = sK0 | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2)) | sK0 = k2_relset_1(X2,sK0,X3) | ~v1_funct_1(sK2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_2(X3,X2,sK0) | ~v1_funct_1(X3)) )),
% 3.94/0.87    inference(subsumption_resolution,[],[f473,f76])).
% 3.94/0.87  fof(f473,plain,(
% 3.94/0.87    ( ! [X2,X3] : (k1_xboole_0 = sK0 | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2)) | sK0 = k2_relset_1(X2,sK0,X3) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_2(X3,X2,sK0) | ~v1_funct_1(X3)) )),
% 3.94/0.87    inference(subsumption_resolution,[],[f386,f191])).
% 3.94/0.87  fof(f386,plain,(
% 3.94/0.87    ( ! [X2,X3] : (k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 != k2_relset_1(X2,sK0,k1_partfun1(X2,sK0,sK0,sK0,X3,sK2)) | sK0 = k2_relset_1(X2,sK0,X3) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_2(X3,X2,sK0) | ~v1_funct_1(X3)) )),
% 3.94/0.87    inference(resolution,[],[f109,f78])).
% 3.94/0.87  fof(f109,plain,(
% 3.94/0.87    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | ~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | k2_relset_1(X0,X1,X3) = X1 | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f58])).
% 3.94/0.87  fof(f58,plain,(
% 3.94/0.87    ! [X0,X1,X2,X3] : (! [X4] : (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2 | ~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.94/0.87    inference(flattening,[],[f57])).
% 3.94/0.87  fof(f57,plain,(
% 3.94/0.87    ! [X0,X1,X2,X3] : (! [X4] : (((k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2) | (~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.94/0.87    inference(ennf_transformation,[],[f20])).
% 3.94/0.87  fof(f20,axiom,(
% 3.94/0.87    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 3.94/0.87  fof(f449,plain,(
% 3.94/0.87    spl5_20 | spl5_4),
% 3.94/0.87    inference(avatar_split_clause,[],[f151,f136,f447])).
% 3.94/0.87  fof(f136,plain,(
% 3.94/0.87    spl5_4 <=> ! [X1] : ~v1_xboole_0(X1)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.94/0.87  fof(f151,plain,(
% 3.94/0.87    ( ! [X4,X5] : (~v1_xboole_0(X4) | ~r2_hidden(X5,k1_xboole_0)) )),
% 3.94/0.87    inference(resolution,[],[f108,f81])).
% 3.94/0.87  fof(f108,plain,(
% 3.94/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f56])).
% 3.94/0.87  fof(f56,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.94/0.87    inference(ennf_transformation,[],[f6])).
% 3.94/0.87  fof(f6,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 3.94/0.87  fof(f423,plain,(
% 3.94/0.87    ~spl5_4),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f422])).
% 3.94/0.87  fof(f422,plain,(
% 3.94/0.87    $false | ~spl5_4),
% 3.94/0.87    inference(resolution,[],[f137,f87])).
% 3.94/0.87  fof(f87,plain,(
% 3.94/0.87    ( ! [X0] : (v1_xboole_0(sK3(X0))) )),
% 3.94/0.87    inference(cnf_transformation,[],[f67])).
% 3.94/0.87  fof(f67,plain,(
% 3.94/0.87    ! [X0] : (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 3.94/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f66])).
% 3.94/0.87  fof(f66,plain,(
% 3.94/0.87    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 3.94/0.87    introduced(choice_axiom,[])).
% 3.94/0.87  fof(f2,axiom,(
% 3.94/0.87    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 3.94/0.87  fof(f137,plain,(
% 3.94/0.87    ( ! [X1] : (~v1_xboole_0(X1)) ) | ~spl5_4),
% 3.94/0.87    inference(avatar_component_clause,[],[f136])).
% 3.94/0.87  fof(f373,plain,(
% 3.94/0.87    spl5_15),
% 3.94/0.87    inference(avatar_contradiction_clause,[],[f372])).
% 3.94/0.87  fof(f372,plain,(
% 3.94/0.87    $false | spl5_15),
% 3.94/0.87    inference(subsumption_resolution,[],[f371,f75])).
% 3.94/0.87  fof(f371,plain,(
% 3.94/0.87    ~v1_funct_1(sK2) | spl5_15),
% 3.94/0.87    inference(subsumption_resolution,[],[f370,f76])).
% 3.94/0.87  fof(f370,plain,(
% 3.94/0.87    ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl5_15),
% 3.94/0.87    inference(subsumption_resolution,[],[f369,f78])).
% 3.94/0.87  fof(f369,plain,(
% 3.94/0.87    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl5_15),
% 3.94/0.87    inference(subsumption_resolution,[],[f368,f71])).
% 3.94/0.87  fof(f368,plain,(
% 3.94/0.87    ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl5_15),
% 3.94/0.87    inference(subsumption_resolution,[],[f367,f72])).
% 3.94/0.87  fof(f367,plain,(
% 3.94/0.87    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl5_15),
% 3.94/0.87    inference(subsumption_resolution,[],[f366,f74])).
% 3.94/0.87  fof(f366,plain,(
% 3.94/0.87    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | spl5_15),
% 3.94/0.87    inference(subsumption_resolution,[],[f365,f354])).
% 3.94/0.87  fof(f354,plain,(
% 3.94/0.87    sK0 != k2_relset_1(sK0,sK0,sK2) | spl5_15),
% 3.94/0.87    inference(avatar_component_clause,[],[f352])).
% 3.94/0.87  fof(f352,plain,(
% 3.94/0.87    spl5_15 <=> sK0 = k2_relset_1(sK0,sK0,sK2)),
% 3.94/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 3.94/0.87  fof(f365,plain,(
% 3.94/0.87    sK0 = k2_relset_1(sK0,sK0,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f105,f79])).
% 3.94/0.87  fof(f105,plain,(
% 3.94/0.87    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f51])).
% 3.94/0.87  fof(f51,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.94/0.87    inference(flattening,[],[f50])).
% 3.94/0.87  fof(f50,plain,(
% 3.94/0.87    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.94/0.87    inference(ennf_transformation,[],[f19])).
% 3.94/0.87  fof(f19,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 3.94/0.87  fof(f355,plain,(
% 3.94/0.87    spl5_14 | ~spl5_15 | spl5_13),
% 3.94/0.87    inference(avatar_split_clause,[],[f346,f340,f352,f348])).
% 3.94/0.87  fof(f346,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 3.94/0.87    inference(subsumption_resolution,[],[f345,f75])).
% 3.94/0.87  fof(f345,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f344,f76])).
% 3.94/0.87  fof(f344,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(subsumption_resolution,[],[f324,f191])).
% 3.94/0.87  fof(f324,plain,(
% 3.94/0.87    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.94/0.87    inference(resolution,[],[f103,f78])).
% 3.94/0.87  fof(f103,plain,(
% 3.94/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.94/0.87    inference(cnf_transformation,[],[f49])).
% 3.94/0.87  fof(f49,plain,(
% 3.94/0.87    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.94/0.87    inference(flattening,[],[f48])).
% 3.94/0.87  fof(f48,plain,(
% 3.94/0.87    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.94/0.87    inference(ennf_transformation,[],[f21])).
% 3.94/0.87  fof(f21,axiom,(
% 3.94/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 3.94/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 3.94/0.87  fof(f236,plain,(
% 3.94/0.87    ~spl5_9 | spl5_10),
% 3.94/0.87    inference(avatar_split_clause,[],[f227,f233,f229])).
% 3.94/0.87  fof(f227,plain,(
% 3.94/0.87    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.87    inference(subsumption_resolution,[],[f226,f82])).
% 3.94/0.87  fof(f226,plain,(
% 3.94/0.87    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.94/0.87    inference(resolution,[],[f110,f79])).
% 3.94/0.87  % SZS output end Proof for theBenchmark
% 3.94/0.87  % (17127)------------------------------
% 3.94/0.87  % (17127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/0.87  % (17127)Termination reason: Refutation
% 3.94/0.87  
% 3.94/0.87  % (17127)Memory used [KB]: 13688
% 3.94/0.87  % (17127)Time elapsed: 0.441 s
% 3.94/0.87  % (17127)------------------------------
% 3.94/0.87  % (17127)------------------------------
% 3.94/0.88  % (17116)Success in time 0.515 s
%------------------------------------------------------------------------------
