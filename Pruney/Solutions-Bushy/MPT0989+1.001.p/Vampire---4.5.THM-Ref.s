%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0989+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:02 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 150 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  227 ( 875 expanded)
%              Number of equality atoms :  101 ( 420 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f67,f70,f84,f91])).

fof(f91,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f88,f56])).

fof(f56,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f55,f24])).

fof(f24,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
      | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2)) )
    & k1_xboole_0 != sK1
    & v2_funct_1(sK2)
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1)
          | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
        & k1_xboole_0 != X1
        & v2_funct_1(X2)
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
        | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2)) )
      & k1_xboole_0 != sK1
      & v2_funct_1(sK2)
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1)
        | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
      & k1_xboole_0 != X1
      & v2_funct_1(X2)
      & k2_relset_1(X0,X1,X2) = X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1)
        | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
      & k1_xboole_0 != X1
      & v2_funct_1(X2)
      & k2_relset_1(X0,X1,X2) = X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & k2_relset_1(X0,X1,X2) = X1 )
         => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
              & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f55,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f88,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f87,f61])).

fof(f61,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f86,f21])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f85,f25])).

fof(f25,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(superposition,[],[f53,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f53,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_relat_1(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_2
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f84,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f80,f49])).

fof(f49,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_1
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(sK0)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f66,f77])).

fof(f77,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f75,f23])).

fof(f75,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f74,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f74,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f73,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f72,f22])).

fof(f22,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f34,f23])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f66,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_4
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f68,f23])).

fof(f68,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_3 ),
    inference(resolution,[],[f62,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f67,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f58,f64,f60])).

fof(f58,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f57,f21])).

fof(f57,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f29,f25])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f40,f51,f47])).

fof(f40,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_relat_1(sK1)
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(sK0) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f28,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f27,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
