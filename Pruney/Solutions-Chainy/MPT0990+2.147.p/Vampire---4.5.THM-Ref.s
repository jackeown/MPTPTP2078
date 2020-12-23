%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:54 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 557 expanded)
%              Number of leaves         :   25 ( 173 expanded)
%              Depth                    :   23
%              Number of atoms          :  587 (5061 expanded)
%              Number of equality atoms :  183 (1757 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f211,f244,f345,f1170])).

fof(f1170,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1169])).

fof(f1169,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1168,f81])).

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

fof(f1168,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f1167,f307])).

fof(f307,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f247,f304])).

fof(f304,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f303,f158])).

fof(f158,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(global_subsumption,[],[f75,f157])).

fof(f157,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f156,f79])).

fof(f79,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f65])).

fof(f156,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f74,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f74,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f303,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f302,f251])).

fof(f251,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,sK0)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f245,f193])).

fof(f193,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f170,f187])).

fof(f187,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f186,f73])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f186,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f185,f74])).

fof(f185,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f184,f75])).

fof(f184,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f183,f70])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f183,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f182,f71])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f182,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f180,f72])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

fof(f180,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f77,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f170,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f75,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f245,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,k2_relat_1(sK3))
    | ~ spl5_3 ),
    inference(resolution,[],[f233,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f233,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl5_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f302,plain,(
    k1_relset_1(sK1,sK0,sK3) = k10_relat_1(sK3,sK0) ),
    inference(forward_demodulation,[],[f169,f167])).

fof(f167,plain,(
    ! [X0] : k8_relset_1(sK1,sK0,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(resolution,[],[f75,f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f169,plain,(
    k1_relset_1(sK1,sK0,sK3) = k8_relset_1(sK1,sK0,sK3,sK0) ),
    inference(resolution,[],[f75,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f247,plain,
    ( sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)
    | ~ spl5_3 ),
    inference(resolution,[],[f233,f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f116,f102])).

fof(f102,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f116,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1167,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f1166,f355])).

fof(f355,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f348,f285])).

fof(f285,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f226,f281])).

fof(f281,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f280,f155])).

fof(f155,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f72,f154])).

fof(f154,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f153,f80])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f65])).

fof(f153,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f71,f90])).

fof(f280,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f279,f219])).

fof(f219,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f213,f188])).

fof(f188,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f162,f76])).

fof(f76,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f162,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f72,f106])).

fof(f213,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f200,f118])).

fof(f200,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f279,plain,(
    k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f161,f159])).

fof(f159,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f72,f123])).

fof(f161,plain,(
    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(resolution,[],[f72,f120])).

fof(f226,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f148,f200])).

fof(f148,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f142,f70])).

fof(f142,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f78,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f348,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl5_5 ),
    inference(resolution,[],[f330,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f117,f102])).

fof(f117,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f330,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl5_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1166,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f1161,f258])).

fof(f258,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f257,f188])).

fof(f257,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f150,f200])).

fof(f150,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f144,f70])).

fof(f144,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f102])).

fof(f84,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1161,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(resolution,[],[f1156,f330])).

fof(f1156,plain,
    ( ! [X14] :
        ( ~ v1_relat_1(X14)
        | k5_relat_1(k5_relat_1(X14,sK2),sK3) = k5_relat_1(X14,k6_partfun1(sK0)) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1145,f438])).

fof(f438,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f435,f437])).

fof(f437,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f436,f129])).

fof(f129,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f111,f102])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f436,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f424,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f424,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f77,f377])).

fof(f377,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f372,f73])).

fof(f372,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f165,f75])).

fof(f165,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | k1_partfun1(sK0,sK1,X2,X3,sK2,X1) = k5_relat_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f163,f70])).

fof(f163,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | k1_partfun1(sK0,sK1,X2,X3,sK2,X1) = k5_relat_1(sK2,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f72,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f435,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f434,f70])).

fof(f434,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f433,f72])).

fof(f433,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f432,f73])).

fof(f432,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f427,f75])).

fof(f427,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f104,f377])).

fof(f104,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1145,plain,
    ( ! [X14] :
        ( ~ v1_relat_1(X14)
        | k5_relat_1(k5_relat_1(X14,sK2),sK3) = k5_relat_1(X14,k5_relat_1(sK2,sK3)) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f217,f233])).

fof(f217,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | k5_relat_1(k5_relat_1(X3,sK2),X2) = k5_relat_1(X3,k5_relat_1(sK2,X2)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f200,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f345,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f343,f200])).

fof(f343,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f341,f70])).

fof(f341,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_5 ),
    inference(resolution,[],[f331,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f331,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f329])).

fof(f244,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f241,f112])).

fof(f112,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f241,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl5_3 ),
    inference(resolution,[],[f240,f75])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_3 ),
    inference(resolution,[],[f234,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f234,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f232])).

fof(f211,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f208,f112])).

fof(f208,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_1 ),
    inference(resolution,[],[f207,f72])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_1 ),
    inference(resolution,[],[f201,f110])).

fof(f201,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:27:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (11404)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (11412)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (11392)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (11388)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (11391)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (11390)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (11396)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (11402)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (11415)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (11405)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (11414)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (11397)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.57  % (11394)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (11417)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (11395)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.57  % (11386)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.67/0.58  % (11406)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.67/0.58  % (11398)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.67/0.58  % (11387)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.67/0.58  % (11408)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.67/0.58  % (11403)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.67/0.58  % (11385)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.67/0.58  % (11403)Refutation not found, incomplete strategy% (11403)------------------------------
% 1.67/0.58  % (11403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (11403)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (11403)Memory used [KB]: 10746
% 1.67/0.58  % (11403)Time elapsed: 0.143 s
% 1.67/0.58  % (11403)------------------------------
% 1.67/0.58  % (11403)------------------------------
% 1.67/0.59  % (11411)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.67/0.59  % (11409)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.67/0.59  % (11400)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.67/0.59  % (11410)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.83/0.60  % (11401)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.83/0.61  % (11399)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.83/0.61  % (11416)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.83/0.62  % (11407)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.07/0.65  % (11411)Refutation found. Thanks to Tanya!
% 2.07/0.65  % SZS status Theorem for theBenchmark
% 2.07/0.66  % SZS output start Proof for theBenchmark
% 2.07/0.66  fof(f1172,plain,(
% 2.07/0.66    $false),
% 2.07/0.66    inference(avatar_sat_refutation,[],[f211,f244,f345,f1170])).
% 2.07/0.66  fof(f1170,plain,(
% 2.07/0.66    ~spl5_1 | ~spl5_3 | ~spl5_5),
% 2.07/0.66    inference(avatar_contradiction_clause,[],[f1169])).
% 2.07/0.66  fof(f1169,plain,(
% 2.07/0.66    $false | (~spl5_1 | ~spl5_3 | ~spl5_5)),
% 2.07/0.66    inference(subsumption_resolution,[],[f1168,f81])).
% 2.07/0.66  fof(f81,plain,(
% 2.07/0.66    k2_funct_1(sK2) != sK3),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f65,plain,(
% 2.07/0.66    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.07/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f64,f63])).
% 2.07/0.66  fof(f63,plain,(
% 2.07/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.07/0.66    introduced(choice_axiom,[])).
% 2.07/0.66  fof(f64,plain,(
% 2.07/0.66    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.07/0.66    introduced(choice_axiom,[])).
% 2.07/0.66  fof(f32,plain,(
% 2.07/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.07/0.66    inference(flattening,[],[f31])).
% 2.07/0.66  fof(f31,plain,(
% 2.07/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.07/0.66    inference(ennf_transformation,[],[f30])).
% 2.07/0.66  fof(f30,negated_conjecture,(
% 2.07/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.07/0.66    inference(negated_conjecture,[],[f29])).
% 2.07/0.66  fof(f29,conjecture,(
% 2.07/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.07/0.66  fof(f1168,plain,(
% 2.07/0.66    k2_funct_1(sK2) = sK3 | (~spl5_1 | ~spl5_3 | ~spl5_5)),
% 2.07/0.66    inference(forward_demodulation,[],[f1167,f307])).
% 2.07/0.66  fof(f307,plain,(
% 2.07/0.66    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl5_3),
% 2.07/0.66    inference(backward_demodulation,[],[f247,f304])).
% 2.07/0.66  fof(f304,plain,(
% 2.07/0.66    sK1 = k1_relat_1(sK3) | ~spl5_3),
% 2.07/0.66    inference(forward_demodulation,[],[f303,f158])).
% 2.07/0.66  fof(f158,plain,(
% 2.07/0.66    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.07/0.66    inference(global_subsumption,[],[f75,f157])).
% 2.07/0.66  fof(f157,plain,(
% 2.07/0.66    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.07/0.66    inference(subsumption_resolution,[],[f156,f79])).
% 2.07/0.66  fof(f79,plain,(
% 2.07/0.66    k1_xboole_0 != sK0),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f156,plain,(
% 2.07/0.66    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.07/0.66    inference(resolution,[],[f74,f90])).
% 2.07/0.66  fof(f90,plain,(
% 2.07/0.66    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.66    inference(cnf_transformation,[],[f66])).
% 2.07/0.66  fof(f66,plain,(
% 2.07/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.66    inference(nnf_transformation,[],[f42])).
% 2.07/0.66  fof(f42,plain,(
% 2.07/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.66    inference(flattening,[],[f41])).
% 2.07/0.66  fof(f41,plain,(
% 2.07/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.66    inference(ennf_transformation,[],[f23])).
% 2.07/0.66  fof(f23,axiom,(
% 2.07/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.07/0.66  fof(f74,plain,(
% 2.07/0.66    v1_funct_2(sK3,sK1,sK0)),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f75,plain,(
% 2.07/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f303,plain,(
% 2.07/0.66    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) | ~spl5_3),
% 2.07/0.66    inference(forward_demodulation,[],[f302,f251])).
% 2.07/0.66  fof(f251,plain,(
% 2.07/0.66    k1_relat_1(sK3) = k10_relat_1(sK3,sK0) | ~spl5_3),
% 2.07/0.66    inference(forward_demodulation,[],[f245,f193])).
% 2.07/0.66  fof(f193,plain,(
% 2.07/0.66    sK0 = k2_relat_1(sK3)),
% 2.07/0.66    inference(forward_demodulation,[],[f170,f187])).
% 2.07/0.66  fof(f187,plain,(
% 2.07/0.66    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.07/0.66    inference(subsumption_resolution,[],[f186,f73])).
% 2.07/0.66  fof(f73,plain,(
% 2.07/0.66    v1_funct_1(sK3)),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f186,plain,(
% 2.07/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 2.07/0.66    inference(subsumption_resolution,[],[f185,f74])).
% 2.07/0.66  fof(f185,plain,(
% 2.07/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.07/0.66    inference(subsumption_resolution,[],[f184,f75])).
% 2.07/0.66  fof(f184,plain,(
% 2.07/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.07/0.66    inference(subsumption_resolution,[],[f183,f70])).
% 2.07/0.66  fof(f70,plain,(
% 2.07/0.66    v1_funct_1(sK2)),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f183,plain,(
% 2.07/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.07/0.66    inference(subsumption_resolution,[],[f182,f71])).
% 2.07/0.66  fof(f71,plain,(
% 2.07/0.66    v1_funct_2(sK2,sK0,sK1)),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f182,plain,(
% 2.07/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.07/0.66    inference(subsumption_resolution,[],[f180,f72])).
% 2.07/0.66  fof(f72,plain,(
% 2.07/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f180,plain,(
% 2.07/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 2.07/0.66    inference(resolution,[],[f77,f101])).
% 2.07/0.66  fof(f101,plain,(
% 2.07/0.66    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f47])).
% 2.07/0.66  fof(f47,plain,(
% 2.07/0.66    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.07/0.66    inference(flattening,[],[f46])).
% 2.07/0.66  fof(f46,plain,(
% 2.07/0.66    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.07/0.66    inference(ennf_transformation,[],[f27])).
% 2.07/0.66  fof(f27,axiom,(
% 2.07/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.07/0.66  fof(f77,plain,(
% 2.07/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f170,plain,(
% 2.07/0.66    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 2.07/0.66    inference(resolution,[],[f75,f106])).
% 2.07/0.66  fof(f106,plain,(
% 2.07/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f52])).
% 2.07/0.66  fof(f52,plain,(
% 2.07/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.66    inference(ennf_transformation,[],[f18])).
% 2.07/0.66  fof(f18,axiom,(
% 2.07/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.07/0.66  fof(f245,plain,(
% 2.07/0.66    k1_relat_1(sK3) = k10_relat_1(sK3,k2_relat_1(sK3)) | ~spl5_3),
% 2.07/0.66    inference(resolution,[],[f233,f118])).
% 2.07/0.66  fof(f118,plain,(
% 2.07/0.66    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f59])).
% 2.07/0.66  fof(f59,plain,(
% 2.07/0.66    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.66    inference(ennf_transformation,[],[f7])).
% 2.07/0.66  fof(f7,axiom,(
% 2.07/0.66    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.07/0.66  fof(f233,plain,(
% 2.07/0.66    v1_relat_1(sK3) | ~spl5_3),
% 2.07/0.66    inference(avatar_component_clause,[],[f232])).
% 2.07/0.66  fof(f232,plain,(
% 2.07/0.66    spl5_3 <=> v1_relat_1(sK3)),
% 2.07/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.07/0.66  fof(f302,plain,(
% 2.07/0.66    k1_relset_1(sK1,sK0,sK3) = k10_relat_1(sK3,sK0)),
% 2.07/0.66    inference(forward_demodulation,[],[f169,f167])).
% 2.07/0.66  fof(f167,plain,(
% 2.07/0.66    ( ! [X0] : (k8_relset_1(sK1,sK0,sK3,X0) = k10_relat_1(sK3,X0)) )),
% 2.07/0.66    inference(resolution,[],[f75,f123])).
% 2.07/0.66  fof(f123,plain,(
% 2.07/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f62])).
% 2.07/0.66  fof(f62,plain,(
% 2.07/0.66    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.66    inference(ennf_transformation,[],[f19])).
% 2.07/0.66  fof(f19,axiom,(
% 2.07/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 2.07/0.66  fof(f169,plain,(
% 2.07/0.66    k1_relset_1(sK1,sK0,sK3) = k8_relset_1(sK1,sK0,sK3,sK0)),
% 2.07/0.66    inference(resolution,[],[f75,f120])).
% 2.07/0.66  fof(f120,plain,(
% 2.07/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f60])).
% 2.07/0.66  fof(f60,plain,(
% 2.07/0.66    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.66    inference(ennf_transformation,[],[f22])).
% 2.07/0.66  fof(f22,axiom,(
% 2.07/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 2.07/0.66  fof(f247,plain,(
% 2.07/0.66    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) | ~spl5_3),
% 2.07/0.66    inference(resolution,[],[f233,f132])).
% 2.07/0.66  fof(f132,plain,(
% 2.07/0.66    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 2.07/0.66    inference(definition_unfolding,[],[f116,f102])).
% 2.07/0.66  fof(f102,plain,(
% 2.07/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f26])).
% 2.07/0.66  fof(f26,axiom,(
% 2.07/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.07/0.66  fof(f116,plain,(
% 2.07/0.66    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f57])).
% 2.07/0.66  fof(f57,plain,(
% 2.07/0.66    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.07/0.66    inference(ennf_transformation,[],[f9])).
% 2.07/0.66  fof(f9,axiom,(
% 2.07/0.66    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.07/0.66  fof(f1167,plain,(
% 2.07/0.66    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl5_1 | ~spl5_3 | ~spl5_5)),
% 2.07/0.66    inference(forward_demodulation,[],[f1166,f355])).
% 2.07/0.66  fof(f355,plain,(
% 2.07/0.66    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl5_1 | ~spl5_5)),
% 2.07/0.66    inference(forward_demodulation,[],[f348,f285])).
% 2.07/0.66  fof(f285,plain,(
% 2.07/0.66    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl5_1),
% 2.07/0.66    inference(backward_demodulation,[],[f226,f281])).
% 2.07/0.66  fof(f281,plain,(
% 2.07/0.66    sK0 = k1_relat_1(sK2) | ~spl5_1),
% 2.07/0.66    inference(forward_demodulation,[],[f280,f155])).
% 2.07/0.66  fof(f155,plain,(
% 2.07/0.66    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.07/0.66    inference(global_subsumption,[],[f72,f154])).
% 2.07/0.66  fof(f154,plain,(
% 2.07/0.66    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.07/0.66    inference(subsumption_resolution,[],[f153,f80])).
% 2.07/0.66  fof(f80,plain,(
% 2.07/0.66    k1_xboole_0 != sK1),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f153,plain,(
% 2.07/0.66    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.07/0.66    inference(resolution,[],[f71,f90])).
% 2.07/0.66  fof(f280,plain,(
% 2.07/0.66    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_1),
% 2.07/0.66    inference(forward_demodulation,[],[f279,f219])).
% 2.07/0.66  fof(f219,plain,(
% 2.07/0.66    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl5_1),
% 2.07/0.66    inference(forward_demodulation,[],[f213,f188])).
% 2.07/0.66  fof(f188,plain,(
% 2.07/0.66    sK1 = k2_relat_1(sK2)),
% 2.07/0.66    inference(forward_demodulation,[],[f162,f76])).
% 2.07/0.66  fof(f76,plain,(
% 2.07/0.66    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f162,plain,(
% 2.07/0.66    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.07/0.66    inference(resolution,[],[f72,f106])).
% 2.07/0.66  fof(f213,plain,(
% 2.07/0.66    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl5_1),
% 2.07/0.66    inference(resolution,[],[f200,f118])).
% 2.07/0.66  fof(f200,plain,(
% 2.07/0.66    v1_relat_1(sK2) | ~spl5_1),
% 2.07/0.66    inference(avatar_component_clause,[],[f199])).
% 2.07/0.66  fof(f199,plain,(
% 2.07/0.66    spl5_1 <=> v1_relat_1(sK2)),
% 2.07/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.07/0.66  fof(f279,plain,(
% 2.07/0.66    k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1)),
% 2.07/0.66    inference(forward_demodulation,[],[f161,f159])).
% 2.07/0.66  fof(f159,plain,(
% 2.07/0.66    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 2.07/0.66    inference(resolution,[],[f72,f123])).
% 2.07/0.66  fof(f161,plain,(
% 2.07/0.66    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 2.07/0.66    inference(resolution,[],[f72,f120])).
% 2.07/0.66  fof(f226,plain,(
% 2.07/0.66    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_1),
% 2.07/0.66    inference(subsumption_resolution,[],[f148,f200])).
% 2.07/0.66  fof(f148,plain,(
% 2.07/0.66    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.07/0.66    inference(subsumption_resolution,[],[f142,f70])).
% 2.07/0.66  fof(f142,plain,(
% 2.07/0.66    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.07/0.66    inference(resolution,[],[f78,f86])).
% 2.07/0.66  fof(f86,plain,(
% 2.07/0.66    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f38])).
% 2.07/0.66  fof(f38,plain,(
% 2.07/0.66    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.66    inference(flattening,[],[f37])).
% 2.07/0.66  fof(f37,plain,(
% 2.07/0.66    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.66    inference(ennf_transformation,[],[f14])).
% 2.07/0.66  fof(f14,axiom,(
% 2.07/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.07/0.66  fof(f78,plain,(
% 2.07/0.66    v2_funct_1(sK2)),
% 2.07/0.66    inference(cnf_transformation,[],[f65])).
% 2.07/0.66  fof(f348,plain,(
% 2.07/0.66    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl5_5),
% 2.07/0.66    inference(resolution,[],[f330,f133])).
% 2.07/0.66  fof(f133,plain,(
% 2.07/0.66    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.07/0.66    inference(definition_unfolding,[],[f117,f102])).
% 2.07/0.66  fof(f117,plain,(
% 2.07/0.66    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f58])).
% 2.07/0.66  fof(f58,plain,(
% 2.07/0.66    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.07/0.66    inference(ennf_transformation,[],[f10])).
% 2.07/0.66  fof(f10,axiom,(
% 2.07/0.66    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.07/0.66  fof(f330,plain,(
% 2.07/0.66    v1_relat_1(k2_funct_1(sK2)) | ~spl5_5),
% 2.07/0.66    inference(avatar_component_clause,[],[f329])).
% 2.07/0.66  fof(f329,plain,(
% 2.07/0.66    spl5_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.07/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.07/0.66  fof(f1166,plain,(
% 2.07/0.66    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl5_1 | ~spl5_3 | ~spl5_5)),
% 2.07/0.66    inference(forward_demodulation,[],[f1161,f258])).
% 2.07/0.66  fof(f258,plain,(
% 2.07/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~spl5_1),
% 2.07/0.66    inference(forward_demodulation,[],[f257,f188])).
% 2.07/0.66  fof(f257,plain,(
% 2.07/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~spl5_1),
% 2.07/0.66    inference(subsumption_resolution,[],[f150,f200])).
% 2.07/0.66  fof(f150,plain,(
% 2.07/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.07/0.66    inference(subsumption_resolution,[],[f144,f70])).
% 2.07/0.66  fof(f144,plain,(
% 2.07/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.07/0.66    inference(resolution,[],[f78,f124])).
% 2.07/0.66  fof(f124,plain,(
% 2.07/0.66    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.66    inference(definition_unfolding,[],[f84,f102])).
% 2.07/0.66  fof(f84,plain,(
% 2.07/0.66    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f36])).
% 2.07/0.66  fof(f36,plain,(
% 2.07/0.66    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.66    inference(flattening,[],[f35])).
% 2.07/0.66  fof(f35,plain,(
% 2.07/0.66    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.66    inference(ennf_transformation,[],[f15])).
% 2.07/0.66  fof(f15,axiom,(
% 2.07/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.07/0.66  fof(f1161,plain,(
% 2.07/0.66    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | (~spl5_1 | ~spl5_3 | ~spl5_5)),
% 2.07/0.66    inference(resolution,[],[f1156,f330])).
% 2.07/0.66  fof(f1156,plain,(
% 2.07/0.66    ( ! [X14] : (~v1_relat_1(X14) | k5_relat_1(k5_relat_1(X14,sK2),sK3) = k5_relat_1(X14,k6_partfun1(sK0))) ) | (~spl5_1 | ~spl5_3)),
% 2.07/0.66    inference(forward_demodulation,[],[f1145,f438])).
% 2.07/0.66  fof(f438,plain,(
% 2.07/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.07/0.66    inference(global_subsumption,[],[f435,f437])).
% 2.07/0.66  fof(f437,plain,(
% 2.07/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.07/0.66    inference(subsumption_resolution,[],[f436,f129])).
% 2.07/0.66  fof(f129,plain,(
% 2.07/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.07/0.66    inference(definition_unfolding,[],[f111,f102])).
% 2.07/0.66  fof(f111,plain,(
% 2.07/0.66    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.07/0.66    inference(cnf_transformation,[],[f21])).
% 2.07/0.66  fof(f21,axiom,(
% 2.07/0.66    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.07/0.66  fof(f436,plain,(
% 2.07/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.07/0.66    inference(resolution,[],[f424,f99])).
% 2.07/0.66  fof(f99,plain,(
% 2.07/0.66    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.66    inference(cnf_transformation,[],[f67])).
% 2.07/0.66  fof(f67,plain,(
% 2.07/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.66    inference(nnf_transformation,[],[f45])).
% 2.07/0.66  fof(f45,plain,(
% 2.07/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.66    inference(flattening,[],[f44])).
% 2.07/0.66  fof(f44,plain,(
% 2.07/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.07/0.66    inference(ennf_transformation,[],[f20])).
% 2.07/0.66  fof(f20,axiom,(
% 2.07/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.07/0.66  fof(f424,plain,(
% 2.07/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.07/0.66    inference(backward_demodulation,[],[f77,f377])).
% 2.07/0.66  fof(f377,plain,(
% 2.07/0.66    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.07/0.66    inference(subsumption_resolution,[],[f372,f73])).
% 2.07/0.66  fof(f372,plain,(
% 2.07/0.66    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.07/0.66    inference(resolution,[],[f165,f75])).
% 2.07/0.66  fof(f165,plain,(
% 2.07/0.66    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X1) | k1_partfun1(sK0,sK1,X2,X3,sK2,X1) = k5_relat_1(sK2,X1)) )),
% 2.07/0.66    inference(subsumption_resolution,[],[f163,f70])).
% 2.07/0.66  fof(f163,plain,(
% 2.07/0.66    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X1) | k1_partfun1(sK0,sK1,X2,X3,sK2,X1) = k5_relat_1(sK2,X1) | ~v1_funct_1(sK2)) )),
% 2.07/0.66    inference(resolution,[],[f72,f105])).
% 2.07/0.66  fof(f105,plain,(
% 2.07/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f51])).
% 2.07/0.66  fof(f51,plain,(
% 2.07/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.07/0.66    inference(flattening,[],[f50])).
% 2.07/0.66  fof(f50,plain,(
% 2.07/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.07/0.66    inference(ennf_transformation,[],[f25])).
% 2.07/0.66  fof(f25,axiom,(
% 2.07/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.07/0.66  fof(f435,plain,(
% 2.07/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.07/0.66    inference(subsumption_resolution,[],[f434,f70])).
% 2.07/0.66  fof(f434,plain,(
% 2.07/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.07/0.66    inference(subsumption_resolution,[],[f433,f72])).
% 2.07/0.66  fof(f433,plain,(
% 2.07/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.07/0.66    inference(subsumption_resolution,[],[f432,f73])).
% 2.07/0.66  fof(f432,plain,(
% 2.07/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.07/0.66    inference(subsumption_resolution,[],[f427,f75])).
% 2.07/0.66  fof(f427,plain,(
% 2.07/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.07/0.66    inference(superposition,[],[f104,f377])).
% 2.07/0.66  fof(f104,plain,(
% 2.07/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f49])).
% 2.07/0.66  fof(f49,plain,(
% 2.07/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.07/0.66    inference(flattening,[],[f48])).
% 2.07/0.66  fof(f48,plain,(
% 2.07/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.07/0.66    inference(ennf_transformation,[],[f24])).
% 2.07/0.66  fof(f24,axiom,(
% 2.07/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.07/0.66  fof(f1145,plain,(
% 2.07/0.66    ( ! [X14] : (~v1_relat_1(X14) | k5_relat_1(k5_relat_1(X14,sK2),sK3) = k5_relat_1(X14,k5_relat_1(sK2,sK3))) ) | (~spl5_1 | ~spl5_3)),
% 2.07/0.66    inference(resolution,[],[f217,f233])).
% 2.07/0.66  fof(f217,plain,(
% 2.07/0.66    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,sK2),X2) = k5_relat_1(X3,k5_relat_1(sK2,X2))) ) | ~spl5_1),
% 2.07/0.66    inference(resolution,[],[f200,f115])).
% 2.07/0.66  fof(f115,plain,(
% 2.07/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.07/0.66    inference(cnf_transformation,[],[f56])).
% 2.07/0.66  fof(f56,plain,(
% 2.07/0.66    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.07/0.66    inference(ennf_transformation,[],[f8])).
% 2.07/0.66  fof(f8,axiom,(
% 2.07/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.07/0.66  fof(f345,plain,(
% 2.07/0.66    ~spl5_1 | spl5_5),
% 2.07/0.66    inference(avatar_contradiction_clause,[],[f344])).
% 2.07/0.66  fof(f344,plain,(
% 2.07/0.66    $false | (~spl5_1 | spl5_5)),
% 2.07/0.66    inference(subsumption_resolution,[],[f343,f200])).
% 2.07/0.66  fof(f343,plain,(
% 2.07/0.66    ~v1_relat_1(sK2) | spl5_5),
% 2.07/0.66    inference(subsumption_resolution,[],[f341,f70])).
% 2.07/0.66  fof(f341,plain,(
% 2.07/0.66    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_5),
% 2.07/0.66    inference(resolution,[],[f331,f87])).
% 2.07/0.66  fof(f87,plain,(
% 2.07/0.66    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f40])).
% 2.07/0.66  fof(f40,plain,(
% 2.07/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.66    inference(flattening,[],[f39])).
% 2.07/0.66  fof(f39,plain,(
% 2.07/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.66    inference(ennf_transformation,[],[f11])).
% 2.07/0.66  fof(f11,axiom,(
% 2.07/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.07/0.66  fof(f331,plain,(
% 2.07/0.66    ~v1_relat_1(k2_funct_1(sK2)) | spl5_5),
% 2.07/0.66    inference(avatar_component_clause,[],[f329])).
% 2.07/0.66  fof(f244,plain,(
% 2.07/0.66    spl5_3),
% 2.07/0.66    inference(avatar_contradiction_clause,[],[f243])).
% 2.07/0.66  fof(f243,plain,(
% 2.07/0.66    $false | spl5_3),
% 2.07/0.66    inference(subsumption_resolution,[],[f241,f112])).
% 2.07/0.66  fof(f112,plain,(
% 2.07/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.07/0.66    inference(cnf_transformation,[],[f6])).
% 2.07/0.66  fof(f6,axiom,(
% 2.07/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.07/0.66  fof(f241,plain,(
% 2.07/0.66    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl5_3),
% 2.07/0.66    inference(resolution,[],[f240,f75])).
% 2.07/0.66  fof(f240,plain,(
% 2.07/0.66    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_3),
% 2.07/0.66    inference(resolution,[],[f234,f110])).
% 2.07/0.66  fof(f110,plain,(
% 2.07/0.66    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.07/0.66    inference(cnf_transformation,[],[f55])).
% 2.07/0.66  fof(f55,plain,(
% 2.07/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.07/0.66    inference(ennf_transformation,[],[f5])).
% 2.07/0.66  fof(f5,axiom,(
% 2.07/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.07/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.07/0.66  fof(f234,plain,(
% 2.07/0.66    ~v1_relat_1(sK3) | spl5_3),
% 2.07/0.66    inference(avatar_component_clause,[],[f232])).
% 2.07/0.66  fof(f211,plain,(
% 2.07/0.66    spl5_1),
% 2.07/0.66    inference(avatar_contradiction_clause,[],[f210])).
% 2.07/0.66  fof(f210,plain,(
% 2.07/0.66    $false | spl5_1),
% 2.07/0.66    inference(subsumption_resolution,[],[f208,f112])).
% 2.07/0.66  fof(f208,plain,(
% 2.07/0.66    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_1),
% 2.07/0.66    inference(resolution,[],[f207,f72])).
% 2.07/0.66  fof(f207,plain,(
% 2.07/0.66    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_1),
% 2.07/0.66    inference(resolution,[],[f201,f110])).
% 2.07/0.66  fof(f201,plain,(
% 2.07/0.66    ~v1_relat_1(sK2) | spl5_1),
% 2.07/0.66    inference(avatar_component_clause,[],[f199])).
% 2.07/0.66  % SZS output end Proof for theBenchmark
% 2.07/0.66  % (11411)------------------------------
% 2.07/0.66  % (11411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.66  % (11411)Termination reason: Refutation
% 2.07/0.66  
% 2.07/0.66  % (11411)Memory used [KB]: 11513
% 2.07/0.66  % (11411)Time elapsed: 0.222 s
% 2.07/0.66  % (11411)------------------------------
% 2.07/0.66  % (11411)------------------------------
% 2.07/0.67  % (11378)Success in time 0.308 s
%------------------------------------------------------------------------------
