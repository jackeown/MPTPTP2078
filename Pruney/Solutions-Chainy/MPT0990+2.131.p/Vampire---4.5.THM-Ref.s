%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:51 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  206 (1753 expanded)
%              Number of leaves         :   27 ( 542 expanded)
%              Depth                    :   28
%              Number of atoms          :  838 (16765 expanded)
%              Number of equality atoms :  210 (5628 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f328,f1009,f2174,f2188,f2383])).

fof(f2383,plain,(
    ~ spl5_71 ),
    inference(avatar_contradiction_clause,[],[f2382])).

fof(f2382,plain,
    ( $false
    | ~ spl5_71 ),
    inference(resolution,[],[f2173,f117])).

fof(f117,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f79,f78])).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f2173,plain,
    ( ! [X6,X7] : ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f2172])).

fof(f2172,plain,
    ( spl5_71
  <=> ! [X7,X6] : ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f2188,plain,(
    ~ spl5_70 ),
    inference(avatar_contradiction_clause,[],[f2187])).

fof(f2187,plain,
    ( $false
    | ~ spl5_70 ),
    inference(subsumption_resolution,[],[f2175,f155])).

fof(f155,plain,(
    sK4 != k4_relat_1(sK3) ),
    inference(superposition,[],[f77,f153])).

fof(f153,plain,(
    k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f152,f137])).

fof(f137,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f134,f94])).

fof(f94,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f134,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f83,f68])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f59,f58])).

fof(f58,plain,
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
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & sK2 = k2_relset_1(sK1,sK2,sK3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X3] :
        ( k2_funct_1(sK3) != X3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & v2_funct_1(sK3)
        & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
        & sK2 = k2_relset_1(sK1,sK2,sK3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X3,sK2,sK1)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK3) != sK4
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & v2_funct_1(sK3)
      & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f152,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f150,f66])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f150,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f86,f74])).

fof(f74,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f77,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f60])).

fof(f2175,plain,
    ( sK4 = k4_relat_1(sK3)
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f143,f2170])).

fof(f2170,plain,
    ( sK3 = k4_relat_1(sK4)
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f2168])).

fof(f2168,plain,
    ( spl5_70
  <=> sK3 = k4_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f143,plain,(
    sK4 = k4_relat_1(k4_relat_1(sK4)) ),
    inference(resolution,[],[f138,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f138,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f135,f94])).

fof(f135,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(resolution,[],[f83,f71])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f2174,plain,
    ( spl5_70
    | spl5_71
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f2166,f322,f2172,f2168])).

fof(f322,plain,
    ( spl5_7
  <=> v2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f2166,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | sK3 = k4_relat_1(sK4) )
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f2165])).

fof(f2165,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | sK3 = k4_relat_1(sK4)
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f2164,f1000])).

fof(f1000,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK4) ),
    inference(global_subsumption,[],[f971,f999])).

fof(f999,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK4)
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(resolution,[],[f954,f402])).

fof(f402,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f112,f117])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f954,plain,(
    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) ),
    inference(backward_demodulation,[],[f73,f638])).

fof(f638,plain,(
    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f634,f66])).

fof(f634,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f496,f68])).

fof(f496,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_partfun1(X10,X11,sK2,sK1,X12,sK4) = k5_relat_1(X12,sK4)
      | ~ v1_funct_1(X12) ) ),
    inference(subsumption_resolution,[],[f493,f69])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f493,plain,(
    ! [X12,X10,X11] :
      ( k1_partfun1(X10,X11,sK2,sK1,X12,sK4) = k5_relat_1(X12,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X12) ) ),
    inference(resolution,[],[f114,f71])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f73,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f971,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f970,f66])).

fof(f970,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f969,f68])).

fof(f969,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f968,f69])).

fof(f968,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f956,f71])).

fof(f956,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f116,f638])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f2164,plain,
    ( ! [X6,X7] :
        ( sK3 = k4_relat_1(sK4)
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f2163,f130])).

fof(f130,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f2163,plain,
    ( ! [X6,X7] :
        ( ~ r2_relset_1(X6,X7,k6_partfun1(sK1),k6_partfun1(sK1))
        | sK3 = k4_relat_1(sK4)
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f2162,f1000])).

fof(f2162,plain,
    ( ! [X6,X7] :
        ( sK3 = k4_relat_1(sK4)
        | ~ r2_relset_1(X6,X7,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f2161,f137])).

fof(f2161,plain,
    ( ! [X6,X7] :
        ( sK3 = k4_relat_1(sK4)
        | ~ r2_relset_1(X6,X7,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f2150,f66])).

fof(f2150,plain,
    ( ! [X6,X7] :
        ( sK3 = k4_relat_1(sK4)
        | ~ r2_relset_1(X6,X7,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f2148])).

fof(f2148,plain,
    ( ! [X6,X7] :
        ( sK2 != sK2
        | sK3 = k4_relat_1(sK4)
        | ~ r2_relset_1(X6,X7,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_7 ),
    inference(superposition,[],[f1336,f516])).

fof(f516,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f483,f512])).

fof(f512,plain,(
    sK2 = k1_relset_1(sK2,sK1,k4_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f511,f75])).

fof(f75,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f511,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,k4_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f510,f438])).

fof(f438,plain,(
    v1_funct_2(k4_relat_1(sK3),sK2,sK1) ),
    inference(forward_demodulation,[],[f437,f153])).

fof(f437,plain,(
    v1_funct_2(k2_funct_1(sK3),sK2,sK1) ),
    inference(subsumption_resolution,[],[f436,f66])).

fof(f436,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f435,f67])).

fof(f67,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f435,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f434,f68])).

fof(f434,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f433,f74])).

fof(f433,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f432])).

fof(f432,plain,
    ( sK2 != sK2
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f108,f72])).

fof(f72,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
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

fof(f510,plain,
    ( ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,k4_relat_1(sK3)) ),
    inference(resolution,[],[f479,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f479,plain,(
    sP0(sK2,k4_relat_1(sK3),sK1) ),
    inference(resolution,[],[f475,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f45,f56])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f475,plain,(
    m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(forward_demodulation,[],[f474,f153])).

fof(f474,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f473,f66])).

fof(f473,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f472,f67])).

fof(f472,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f471,f68])).

fof(f471,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f470,f74])).

fof(f470,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f469])).

fof(f469,plain,
    ( sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f109,f72])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f483,plain,(
    k2_relat_1(sK3) = k1_relset_1(sK2,sK1,k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f477,f170])).

fof(f170,plain,(
    k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f169,f153])).

fof(f169,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f168,f137])).

fof(f168,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f166,f66])).

fof(f166,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f87,f74])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f477,plain,(
    k1_relat_1(k4_relat_1(sK3)) = k1_relset_1(sK2,sK1,k4_relat_1(sK3)) ),
    inference(resolution,[],[f475,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1336,plain,
    ( ! [X2,X0,X1] :
        ( k2_relat_1(X0) != sK2
        | k4_relat_1(sK4) = X0
        | ~ r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1335,f542])).

fof(f542,plain,(
    sK1 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f541,f138])).

fof(f541,plain,
    ( sK1 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f540,f145])).

fof(f145,plain,(
    v5_relat_1(sK4,sK1) ),
    inference(resolution,[],[f99,f71])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f540,plain,
    ( sK1 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,sK1)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f539,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f539,plain,(
    v2_funct_2(sK4,sK1) ),
    inference(subsumption_resolution,[],[f538,f66])).

fof(f538,plain,
    ( v2_funct_2(sK4,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f537,f67])).

fof(f537,plain,
    ( v2_funct_2(sK4,sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f536,f68])).

fof(f536,plain,
    ( v2_funct_2(sK4,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f535,f69])).

fof(f535,plain,
    ( v2_funct_2(sK4,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f534,f70])).

fof(f70,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f534,plain,
    ( v2_funct_2(sK4,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f533,f71])).

fof(f533,plain,
    ( v2_funct_2(sK4,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f111,f73])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f1335,plain,
    ( ! [X2,X0,X1] :
        ( k4_relat_1(sK4) = X0
        | ~ r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(sK1))
        | k2_relat_1(X0) != sK2
        | ~ m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1334,f345])).

fof(f345,plain,
    ( k4_relat_1(sK4) = k2_funct_1(sK4)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f344,f138])).

fof(f344,plain,
    ( k4_relat_1(sK4) = k2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f333,f69])).

fof(f333,plain,
    ( k4_relat_1(sK4) = k2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(resolution,[],[f324,f86])).

fof(f324,plain,
    ( v2_funct_1(sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f322])).

fof(f1334,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(sK1))
        | k2_relat_1(X0) != sK2
        | ~ m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k2_funct_1(sK4) = X0
        | ~ m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1333,f542])).

fof(f1333,plain,
    ( ! [X2,X0,X1] :
        ( k2_relat_1(X0) != sK2
        | ~ r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(k2_relat_1(sK4)))
        | ~ m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k2_funct_1(sK4) = X0
        | ~ m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1332,f138])).

fof(f1332,plain,
    ( ! [X2,X0,X1] :
        ( k2_relat_1(X0) != sK2
        | ~ r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(k2_relat_1(sK4)))
        | ~ m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k2_funct_1(sK4) = X0
        | ~ m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1331,f69])).

fof(f1331,plain,
    ( ! [X2,X0,X1] :
        ( k2_relat_1(X0) != sK2
        | ~ r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(k2_relat_1(sK4)))
        | ~ m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k2_funct_1(sK4) = X0
        | ~ m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1323,f324])).

fof(f1323,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) != sK2
      | ~ r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(k2_relat_1(sK4)))
      | ~ m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_funct_1(sK4) = X0
      | ~ m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f453,f264])).

fof(f264,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f199,f252])).

fof(f252,plain,(
    sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f251,f75])).

fof(f251,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f247,f70])).

fof(f247,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(resolution,[],[f100,f148])).

fof(f148,plain,(
    sP0(sK2,sK4,sK1) ),
    inference(resolution,[],[f104,f71])).

fof(f199,plain,(
    k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f97,f71])).

fof(f453,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X3)
      | ~ r2_relset_1(X1,X2,k5_relat_1(X3,X0),k6_partfun1(k2_relat_1(X0)))
      | ~ m1_subset_1(k5_relat_1(X3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_funct_1(X0) = X3
      | ~ m1_subset_1(k6_partfun1(k2_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(extensionality_resolution,[],[f112,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f91,f78])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f1009,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1008])).

fof(f1008,plain,
    ( $false
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f1001,f118])).

fof(f118,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f81,f78])).

fof(f81,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1001,plain,
    ( ~ v2_funct_1(k6_partfun1(sK1))
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f529,f1000])).

fof(f529,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f528,f66])).

fof(f528,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f522,f137])).

fof(f522,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_8 ),
    inference(trivial_inequality_removal,[],[f520])).

fof(f520,plain,
    ( sK2 != sK2
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_8 ),
    inference(superposition,[],[f327,f516])).

fof(f327,plain,
    ( ! [X2] :
        ( sK2 != k2_relat_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v2_funct_1(k5_relat_1(X2,sK4)) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl5_8
  <=> ! [X2] :
        ( sK2 != k2_relat_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v2_funct_1(k5_relat_1(X2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f328,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f320,f326,f322])).

fof(f320,plain,(
    ! [X2] :
      ( sK2 != k2_relat_1(X2)
      | v2_funct_1(sK4)
      | ~ v2_funct_1(k5_relat_1(X2,sK4))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f319,f138])).

fof(f319,plain,(
    ! [X2] :
      ( sK2 != k2_relat_1(X2)
      | v2_funct_1(sK4)
      | ~ v2_funct_1(k5_relat_1(X2,sK4))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f316,f69])).

fof(f316,plain,(
    ! [X2] :
      ( sK2 != k2_relat_1(X2)
      | v2_funct_1(sK4)
      | ~ v2_funct_1(k5_relat_1(X2,sK4))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f93,f264])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (26418)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (26414)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (26415)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (26420)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (26440)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (26421)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (26419)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (26429)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (26438)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (26434)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (26416)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (26422)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (26427)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (26431)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (26436)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (26441)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (26433)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.55  % (26412)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.55  % (26437)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.36/0.55  % (26425)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.55  % (26426)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.55  % (26424)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.36/0.56  % (26430)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.56  % (26432)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.36/0.56  % (26435)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.56  % (26417)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.56  % (26423)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.51/0.57  % (26428)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.51/0.57  % (26428)Refutation not found, incomplete strategy% (26428)------------------------------
% 1.51/0.57  % (26428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (26428)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (26428)Memory used [KB]: 10746
% 1.51/0.57  % (26428)Time elapsed: 0.149 s
% 1.51/0.57  % (26428)------------------------------
% 1.51/0.57  % (26428)------------------------------
% 1.51/0.57  % (26413)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.51/0.59  % (26439)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.00/0.66  % (26418)Refutation found. Thanks to Tanya!
% 2.00/0.66  % SZS status Theorem for theBenchmark
% 2.00/0.66  % SZS output start Proof for theBenchmark
% 2.00/0.66  fof(f2384,plain,(
% 2.00/0.66    $false),
% 2.00/0.66    inference(avatar_sat_refutation,[],[f328,f1009,f2174,f2188,f2383])).
% 2.00/0.66  fof(f2383,plain,(
% 2.00/0.66    ~spl5_71),
% 2.00/0.66    inference(avatar_contradiction_clause,[],[f2382])).
% 2.00/0.66  fof(f2382,plain,(
% 2.00/0.66    $false | ~spl5_71),
% 2.00/0.66    inference(resolution,[],[f2173,f117])).
% 2.00/0.66  fof(f117,plain,(
% 2.00/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.00/0.66    inference(definition_unfolding,[],[f79,f78])).
% 2.00/0.66  fof(f78,plain,(
% 2.00/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f19])).
% 2.00/0.66  fof(f19,axiom,(
% 2.00/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.00/0.66  fof(f79,plain,(
% 2.00/0.66    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.00/0.66    inference(cnf_transformation,[],[f14])).
% 2.00/0.66  fof(f14,axiom,(
% 2.00/0.66    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.00/0.66  fof(f2173,plain,(
% 2.00/0.66    ( ! [X6,X7] : (~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl5_71),
% 2.00/0.66    inference(avatar_component_clause,[],[f2172])).
% 2.00/0.66  fof(f2172,plain,(
% 2.00/0.66    spl5_71 <=> ! [X7,X6] : ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))),
% 2.00/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 2.00/0.66  fof(f2188,plain,(
% 2.00/0.66    ~spl5_70),
% 2.00/0.66    inference(avatar_contradiction_clause,[],[f2187])).
% 2.00/0.66  fof(f2187,plain,(
% 2.00/0.66    $false | ~spl5_70),
% 2.00/0.66    inference(subsumption_resolution,[],[f2175,f155])).
% 2.00/0.66  fof(f155,plain,(
% 2.00/0.66    sK4 != k4_relat_1(sK3)),
% 2.00/0.66    inference(superposition,[],[f77,f153])).
% 2.00/0.66  fof(f153,plain,(
% 2.00/0.66    k2_funct_1(sK3) = k4_relat_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f152,f137])).
% 2.00/0.66  fof(f137,plain,(
% 2.00/0.66    v1_relat_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f134,f94])).
% 2.00/0.66  fof(f94,plain,(
% 2.00/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.00/0.66    inference(cnf_transformation,[],[f2])).
% 2.00/0.66  fof(f2,axiom,(
% 2.00/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.00/0.66  fof(f134,plain,(
% 2.00/0.66    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 2.00/0.66    inference(resolution,[],[f83,f68])).
% 2.00/0.66  fof(f68,plain,(
% 2.00/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f60,plain,(
% 2.00/0.66    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.00/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f59,f58])).
% 2.00/0.66  fof(f58,plain,(
% 2.00/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f59,plain,(
% 2.00/0.66    ? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) => (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f25,plain,(
% 2.00/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.00/0.66    inference(flattening,[],[f24])).
% 2.00/0.66  fof(f24,plain,(
% 2.00/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.00/0.66    inference(ennf_transformation,[],[f23])).
% 2.00/0.66  fof(f23,negated_conjecture,(
% 2.00/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.00/0.66    inference(negated_conjecture,[],[f22])).
% 2.00/0.66  fof(f22,conjecture,(
% 2.00/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.00/0.66  fof(f83,plain,(
% 2.00/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f27])).
% 2.00/0.66  fof(f27,plain,(
% 2.00/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.00/0.66    inference(ennf_transformation,[],[f1])).
% 2.00/0.66  fof(f1,axiom,(
% 2.00/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.00/0.66  fof(f152,plain,(
% 2.00/0.66    k2_funct_1(sK3) = k4_relat_1(sK3) | ~v1_relat_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f150,f66])).
% 2.00/0.66  fof(f66,plain,(
% 2.00/0.66    v1_funct_1(sK3)),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f150,plain,(
% 2.00/0.66    k2_funct_1(sK3) = k4_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.00/0.66    inference(resolution,[],[f86,f74])).
% 2.00/0.66  fof(f74,plain,(
% 2.00/0.66    v2_funct_1(sK3)),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f86,plain,(
% 2.00/0.66    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f31])).
% 2.00/0.66  fof(f31,plain,(
% 2.00/0.66    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.00/0.66    inference(flattening,[],[f30])).
% 2.00/0.66  fof(f30,plain,(
% 2.00/0.66    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.00/0.66    inference(ennf_transformation,[],[f4])).
% 2.00/0.66  fof(f4,axiom,(
% 2.00/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 2.00/0.66  fof(f77,plain,(
% 2.00/0.66    k2_funct_1(sK3) != sK4),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f2175,plain,(
% 2.00/0.66    sK4 = k4_relat_1(sK3) | ~spl5_70),
% 2.00/0.66    inference(backward_demodulation,[],[f143,f2170])).
% 2.00/0.66  fof(f2170,plain,(
% 2.00/0.66    sK3 = k4_relat_1(sK4) | ~spl5_70),
% 2.00/0.66    inference(avatar_component_clause,[],[f2168])).
% 2.00/0.66  fof(f2168,plain,(
% 2.00/0.66    spl5_70 <=> sK3 = k4_relat_1(sK4)),
% 2.00/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 2.00/0.66  fof(f143,plain,(
% 2.00/0.66    sK4 = k4_relat_1(k4_relat_1(sK4))),
% 2.00/0.66    inference(resolution,[],[f138,f82])).
% 2.00/0.66  fof(f82,plain,(
% 2.00/0.66    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 2.00/0.66    inference(cnf_transformation,[],[f26])).
% 2.00/0.66  fof(f26,plain,(
% 2.00/0.66    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.00/0.66    inference(ennf_transformation,[],[f3])).
% 2.00/0.66  fof(f3,axiom,(
% 2.00/0.66    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 2.00/0.66  fof(f138,plain,(
% 2.00/0.66    v1_relat_1(sK4)),
% 2.00/0.66    inference(subsumption_resolution,[],[f135,f94])).
% 2.00/0.66  fof(f135,plain,(
% 2.00/0.66    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK1))),
% 2.00/0.66    inference(resolution,[],[f83,f71])).
% 2.00/0.66  fof(f71,plain,(
% 2.00/0.66    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f2174,plain,(
% 2.00/0.66    spl5_70 | spl5_71 | ~spl5_7),
% 2.00/0.66    inference(avatar_split_clause,[],[f2166,f322,f2172,f2168])).
% 2.00/0.66  fof(f322,plain,(
% 2.00/0.66    spl5_7 <=> v2_funct_1(sK4)),
% 2.00/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.00/0.66  fof(f2166,plain,(
% 2.00/0.66    ( ! [X6,X7] : (~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | sK3 = k4_relat_1(sK4)) ) | ~spl5_7),
% 2.00/0.66    inference(duplicate_literal_removal,[],[f2165])).
% 2.00/0.66  fof(f2165,plain,(
% 2.00/0.66    ( ! [X6,X7] : (~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | sK3 = k4_relat_1(sK4) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl5_7),
% 2.00/0.66    inference(forward_demodulation,[],[f2164,f1000])).
% 2.00/0.66  fof(f1000,plain,(
% 2.00/0.66    k6_partfun1(sK1) = k5_relat_1(sK3,sK4)),
% 2.00/0.66    inference(global_subsumption,[],[f971,f999])).
% 2.00/0.66  fof(f999,plain,(
% 2.00/0.66    k6_partfun1(sK1) = k5_relat_1(sK3,sK4) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.00/0.66    inference(resolution,[],[f954,f402])).
% 2.00/0.66  fof(f402,plain,(
% 2.00/0.66    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.00/0.66    inference(resolution,[],[f112,f117])).
% 2.00/0.66  fof(f112,plain,(
% 2.00/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.66    inference(cnf_transformation,[],[f65])).
% 2.00/0.66  fof(f65,plain,(
% 2.00/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.66    inference(nnf_transformation,[],[f51])).
% 2.00/0.66  fof(f51,plain,(
% 2.00/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.66    inference(flattening,[],[f50])).
% 2.00/0.66  fof(f50,plain,(
% 2.00/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.00/0.66    inference(ennf_transformation,[],[f13])).
% 2.00/0.66  fof(f13,axiom,(
% 2.00/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.00/0.66  fof(f954,plain,(
% 2.00/0.66    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1))),
% 2.00/0.66    inference(backward_demodulation,[],[f73,f638])).
% 2.00/0.66  fof(f638,plain,(
% 2.00/0.66    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 2.00/0.66    inference(subsumption_resolution,[],[f634,f66])).
% 2.00/0.66  fof(f634,plain,(
% 2.00/0.66    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(resolution,[],[f496,f68])).
% 2.00/0.66  fof(f496,plain,(
% 2.00/0.66    ( ! [X12,X10,X11] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | k1_partfun1(X10,X11,sK2,sK1,X12,sK4) = k5_relat_1(X12,sK4) | ~v1_funct_1(X12)) )),
% 2.00/0.66    inference(subsumption_resolution,[],[f493,f69])).
% 2.00/0.66  fof(f69,plain,(
% 2.00/0.66    v1_funct_1(sK4)),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f493,plain,(
% 2.00/0.66    ( ! [X12,X10,X11] : (k1_partfun1(X10,X11,sK2,sK1,X12,sK4) = k5_relat_1(X12,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(X12)) )),
% 2.00/0.66    inference(resolution,[],[f114,f71])).
% 2.00/0.66  fof(f114,plain,(
% 2.00/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f53])).
% 2.00/0.66  fof(f53,plain,(
% 2.00/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.00/0.66    inference(flattening,[],[f52])).
% 2.00/0.66  fof(f52,plain,(
% 2.00/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.00/0.66    inference(ennf_transformation,[],[f18])).
% 2.00/0.66  fof(f18,axiom,(
% 2.00/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.00/0.66  fof(f73,plain,(
% 2.00/0.66    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f971,plain,(
% 2.00/0.66    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.00/0.66    inference(subsumption_resolution,[],[f970,f66])).
% 2.00/0.66  fof(f970,plain,(
% 2.00/0.66    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f969,f68])).
% 2.00/0.66  fof(f969,plain,(
% 2.00/0.66    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f968,f69])).
% 2.00/0.66  fof(f968,plain,(
% 2.00/0.66    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f956,f71])).
% 2.00/0.66  fof(f956,plain,(
% 2.00/0.66    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(superposition,[],[f116,f638])).
% 2.00/0.66  fof(f116,plain,(
% 2.00/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f55])).
% 2.00/0.66  fof(f55,plain,(
% 2.00/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.00/0.66    inference(flattening,[],[f54])).
% 2.00/0.66  fof(f54,plain,(
% 2.00/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.00/0.66    inference(ennf_transformation,[],[f17])).
% 2.00/0.66  fof(f17,axiom,(
% 2.00/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.00/0.66  fof(f2164,plain,(
% 2.00/0.66    ( ! [X6,X7] : (sK3 = k4_relat_1(sK4) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl5_7),
% 2.00/0.66    inference(subsumption_resolution,[],[f2163,f130])).
% 2.00/0.66  fof(f130,plain,(
% 2.00/0.66    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 2.00/0.66    inference(duplicate_literal_removal,[],[f129])).
% 2.00/0.66  fof(f129,plain,(
% 2.00/0.66    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.66    inference(equality_resolution,[],[f113])).
% 2.00/0.66  fof(f113,plain,(
% 2.00/0.66    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.66    inference(cnf_transformation,[],[f65])).
% 2.00/0.66  fof(f2163,plain,(
% 2.00/0.66    ( ! [X6,X7] : (~r2_relset_1(X6,X7,k6_partfun1(sK1),k6_partfun1(sK1)) | sK3 = k4_relat_1(sK4) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl5_7),
% 2.00/0.66    inference(forward_demodulation,[],[f2162,f1000])).
% 2.00/0.66  fof(f2162,plain,(
% 2.00/0.66    ( ! [X6,X7] : (sK3 = k4_relat_1(sK4) | ~r2_relset_1(X6,X7,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl5_7),
% 2.00/0.66    inference(subsumption_resolution,[],[f2161,f137])).
% 2.00/0.66  fof(f2161,plain,(
% 2.00/0.66    ( ! [X6,X7] : (sK3 = k4_relat_1(sK4) | ~r2_relset_1(X6,X7,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_relat_1(sK3)) ) | ~spl5_7),
% 2.00/0.66    inference(subsumption_resolution,[],[f2150,f66])).
% 2.00/0.66  fof(f2150,plain,(
% 2.00/0.66    ( ! [X6,X7] : (sK3 = k4_relat_1(sK4) | ~r2_relset_1(X6,X7,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_7),
% 2.00/0.66    inference(trivial_inequality_removal,[],[f2148])).
% 2.00/0.66  fof(f2148,plain,(
% 2.00/0.66    ( ! [X6,X7] : (sK2 != sK2 | sK3 = k4_relat_1(sK4) | ~r2_relset_1(X6,X7,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_7),
% 2.00/0.66    inference(superposition,[],[f1336,f516])).
% 2.00/0.66  fof(f516,plain,(
% 2.00/0.66    sK2 = k2_relat_1(sK3)),
% 2.00/0.66    inference(forward_demodulation,[],[f483,f512])).
% 2.00/0.66  fof(f512,plain,(
% 2.00/0.66    sK2 = k1_relset_1(sK2,sK1,k4_relat_1(sK3))),
% 2.00/0.66    inference(subsumption_resolution,[],[f511,f75])).
% 2.00/0.66  fof(f75,plain,(
% 2.00/0.66    k1_xboole_0 != sK1),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f511,plain,(
% 2.00/0.66    k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,k4_relat_1(sK3))),
% 2.00/0.66    inference(subsumption_resolution,[],[f510,f438])).
% 2.00/0.66  fof(f438,plain,(
% 2.00/0.66    v1_funct_2(k4_relat_1(sK3),sK2,sK1)),
% 2.00/0.66    inference(forward_demodulation,[],[f437,f153])).
% 2.00/0.66  fof(f437,plain,(
% 2.00/0.66    v1_funct_2(k2_funct_1(sK3),sK2,sK1)),
% 2.00/0.66    inference(subsumption_resolution,[],[f436,f66])).
% 2.00/0.66  fof(f436,plain,(
% 2.00/0.66    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f435,f67])).
% 2.00/0.66  fof(f67,plain,(
% 2.00/0.66    v1_funct_2(sK3,sK1,sK2)),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f435,plain,(
% 2.00/0.66    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f434,f68])).
% 2.00/0.66  fof(f434,plain,(
% 2.00/0.66    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f433,f74])).
% 2.00/0.66  fof(f433,plain,(
% 2.00/0.66    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(trivial_inequality_removal,[],[f432])).
% 2.00/0.66  fof(f432,plain,(
% 2.00/0.66    sK2 != sK2 | v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(superposition,[],[f108,f72])).
% 2.00/0.66  fof(f72,plain,(
% 2.00/0.66    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f108,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f47])).
% 2.00/0.66  fof(f47,plain,(
% 2.00/0.66    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.00/0.66    inference(flattening,[],[f46])).
% 2.00/0.66  fof(f46,plain,(
% 2.00/0.66    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.00/0.66    inference(ennf_transformation,[],[f21])).
% 2.00/0.66  fof(f21,axiom,(
% 2.00/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.00/0.66  fof(f510,plain,(
% 2.00/0.66    ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,k4_relat_1(sK3))),
% 2.00/0.66    inference(resolution,[],[f479,f100])).
% 2.00/0.66  fof(f100,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 2.00/0.66    inference(cnf_transformation,[],[f63])).
% 2.00/0.66  fof(f63,plain,(
% 2.00/0.66    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 2.00/0.66    inference(rectify,[],[f62])).
% 2.00/0.66  fof(f62,plain,(
% 2.00/0.66    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 2.00/0.66    inference(nnf_transformation,[],[f56])).
% 2.00/0.66  fof(f56,plain,(
% 2.00/0.66    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 2.00/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.00/0.66  fof(f479,plain,(
% 2.00/0.66    sP0(sK2,k4_relat_1(sK3),sK1)),
% 2.00/0.66    inference(resolution,[],[f475,f104])).
% 2.00/0.66  fof(f104,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f64])).
% 2.00/0.66  fof(f64,plain,(
% 2.00/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.66    inference(nnf_transformation,[],[f57])).
% 2.00/0.66  fof(f57,plain,(
% 2.00/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.66    inference(definition_folding,[],[f45,f56])).
% 2.00/0.66  fof(f45,plain,(
% 2.00/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.66    inference(flattening,[],[f44])).
% 2.00/0.66  fof(f44,plain,(
% 2.00/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.66    inference(ennf_transformation,[],[f15])).
% 2.00/0.66  fof(f15,axiom,(
% 2.00/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.00/0.66  fof(f475,plain,(
% 2.00/0.66    m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.00/0.66    inference(forward_demodulation,[],[f474,f153])).
% 2.00/0.66  fof(f474,plain,(
% 2.00/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.00/0.66    inference(subsumption_resolution,[],[f473,f66])).
% 2.00/0.66  fof(f473,plain,(
% 2.00/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f472,f67])).
% 2.00/0.66  fof(f472,plain,(
% 2.00/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f471,f68])).
% 2.00/0.66  fof(f471,plain,(
% 2.00/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f470,f74])).
% 2.00/0.66  fof(f470,plain,(
% 2.00/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(trivial_inequality_removal,[],[f469])).
% 2.00/0.66  fof(f469,plain,(
% 2.00/0.66    sK2 != sK2 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(superposition,[],[f109,f72])).
% 2.00/0.66  fof(f109,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f47])).
% 2.00/0.66  fof(f483,plain,(
% 2.00/0.66    k2_relat_1(sK3) = k1_relset_1(sK2,sK1,k4_relat_1(sK3))),
% 2.00/0.66    inference(forward_demodulation,[],[f477,f170])).
% 2.00/0.66  fof(f170,plain,(
% 2.00/0.66    k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3))),
% 2.00/0.66    inference(forward_demodulation,[],[f169,f153])).
% 2.00/0.66  fof(f169,plain,(
% 2.00/0.66    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.00/0.66    inference(subsumption_resolution,[],[f168,f137])).
% 2.00/0.66  fof(f168,plain,(
% 2.00/0.66    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f166,f66])).
% 2.00/0.66  fof(f166,plain,(
% 2.00/0.66    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.00/0.66    inference(resolution,[],[f87,f74])).
% 2.00/0.66  fof(f87,plain,(
% 2.00/0.66    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f33])).
% 2.00/0.66  fof(f33,plain,(
% 2.00/0.66    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.00/0.66    inference(flattening,[],[f32])).
% 2.00/0.66  fof(f32,plain,(
% 2.00/0.66    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.00/0.66    inference(ennf_transformation,[],[f8])).
% 2.00/0.66  fof(f8,axiom,(
% 2.00/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.00/0.66  fof(f477,plain,(
% 2.00/0.66    k1_relat_1(k4_relat_1(sK3)) = k1_relset_1(sK2,sK1,k4_relat_1(sK3))),
% 2.00/0.66    inference(resolution,[],[f475,f97])).
% 2.00/0.66  fof(f97,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f42])).
% 2.00/0.66  fof(f42,plain,(
% 2.00/0.66    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.66    inference(ennf_transformation,[],[f12])).
% 2.00/0.66  fof(f12,axiom,(
% 2.00/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.00/0.66  fof(f1336,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k2_relat_1(X0) != sK2 | k4_relat_1(sK4) = X0 | ~r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_7),
% 2.00/0.66    inference(forward_demodulation,[],[f1335,f542])).
% 2.00/0.66  fof(f542,plain,(
% 2.00/0.66    sK1 = k2_relat_1(sK4)),
% 2.00/0.66    inference(subsumption_resolution,[],[f541,f138])).
% 2.00/0.66  fof(f541,plain,(
% 2.00/0.66    sK1 = k2_relat_1(sK4) | ~v1_relat_1(sK4)),
% 2.00/0.66    inference(subsumption_resolution,[],[f540,f145])).
% 2.00/0.66  fof(f145,plain,(
% 2.00/0.66    v5_relat_1(sK4,sK1)),
% 2.00/0.66    inference(resolution,[],[f99,f71])).
% 2.00/0.66  fof(f99,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f43])).
% 2.00/0.66  fof(f43,plain,(
% 2.00/0.66    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.66    inference(ennf_transformation,[],[f11])).
% 2.00/0.66  fof(f11,axiom,(
% 2.00/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.00/0.66  fof(f540,plain,(
% 2.00/0.66    sK1 = k2_relat_1(sK4) | ~v5_relat_1(sK4,sK1) | ~v1_relat_1(sK4)),
% 2.00/0.66    inference(resolution,[],[f539,f95])).
% 2.00/0.66  fof(f95,plain,(
% 2.00/0.66    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f61])).
% 2.00/0.66  fof(f61,plain,(
% 2.00/0.66    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.00/0.66    inference(nnf_transformation,[],[f41])).
% 2.00/0.66  fof(f41,plain,(
% 2.00/0.66    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.00/0.66    inference(flattening,[],[f40])).
% 2.00/0.66  fof(f40,plain,(
% 2.00/0.66    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.00/0.66    inference(ennf_transformation,[],[f16])).
% 2.00/0.66  fof(f16,axiom,(
% 2.00/0.66    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 2.00/0.66  fof(f539,plain,(
% 2.00/0.66    v2_funct_2(sK4,sK1)),
% 2.00/0.66    inference(subsumption_resolution,[],[f538,f66])).
% 2.00/0.66  fof(f538,plain,(
% 2.00/0.66    v2_funct_2(sK4,sK1) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f537,f67])).
% 2.00/0.66  fof(f537,plain,(
% 2.00/0.66    v2_funct_2(sK4,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f536,f68])).
% 2.00/0.66  fof(f536,plain,(
% 2.00/0.66    v2_funct_2(sK4,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f535,f69])).
% 2.00/0.66  fof(f535,plain,(
% 2.00/0.66    v2_funct_2(sK4,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f534,f70])).
% 2.00/0.66  fof(f70,plain,(
% 2.00/0.66    v1_funct_2(sK4,sK2,sK1)),
% 2.00/0.66    inference(cnf_transformation,[],[f60])).
% 2.00/0.66  fof(f534,plain,(
% 2.00/0.66    v2_funct_2(sK4,sK1) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(subsumption_resolution,[],[f533,f71])).
% 2.00/0.66  fof(f533,plain,(
% 2.00/0.66    v2_funct_2(sK4,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.66    inference(resolution,[],[f111,f73])).
% 2.00/0.66  fof(f111,plain,(
% 2.00/0.66    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f49])).
% 2.00/0.66  fof(f49,plain,(
% 2.00/0.66    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.00/0.66    inference(flattening,[],[f48])).
% 2.00/0.66  fof(f48,plain,(
% 2.00/0.66    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.00/0.66    inference(ennf_transformation,[],[f20])).
% 2.00/0.66  fof(f20,axiom,(
% 2.00/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 2.00/0.66  fof(f1335,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k4_relat_1(sK4) = X0 | ~r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(sK1)) | k2_relat_1(X0) != sK2 | ~m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_7),
% 2.00/0.66    inference(forward_demodulation,[],[f1334,f345])).
% 2.00/0.66  fof(f345,plain,(
% 2.00/0.66    k4_relat_1(sK4) = k2_funct_1(sK4) | ~spl5_7),
% 2.00/0.66    inference(subsumption_resolution,[],[f344,f138])).
% 2.00/0.66  fof(f344,plain,(
% 2.00/0.66    k4_relat_1(sK4) = k2_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl5_7),
% 2.00/0.66    inference(subsumption_resolution,[],[f333,f69])).
% 2.00/0.66  fof(f333,plain,(
% 2.00/0.66    k4_relat_1(sK4) = k2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl5_7),
% 2.00/0.66    inference(resolution,[],[f324,f86])).
% 2.00/0.66  fof(f324,plain,(
% 2.00/0.66    v2_funct_1(sK4) | ~spl5_7),
% 2.00/0.66    inference(avatar_component_clause,[],[f322])).
% 2.00/0.66  fof(f1334,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (~r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(sK1)) | k2_relat_1(X0) != sK2 | ~m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK4) = X0 | ~m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_7),
% 2.00/0.66    inference(forward_demodulation,[],[f1333,f542])).
% 2.00/0.66  fof(f1333,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k2_relat_1(X0) != sK2 | ~r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(k2_relat_1(sK4))) | ~m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK4) = X0 | ~m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_7),
% 2.00/0.66    inference(subsumption_resolution,[],[f1332,f138])).
% 2.00/0.66  fof(f1332,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k2_relat_1(X0) != sK2 | ~r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(k2_relat_1(sK4))) | ~m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK4) = X0 | ~m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK4)) ) | ~spl5_7),
% 2.00/0.66    inference(subsumption_resolution,[],[f1331,f69])).
% 2.00/0.66  fof(f1331,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k2_relat_1(X0) != sK2 | ~r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(k2_relat_1(sK4))) | ~m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK4) = X0 | ~m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | ~spl5_7),
% 2.00/0.66    inference(subsumption_resolution,[],[f1323,f324])).
% 2.00/0.66  fof(f1323,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k2_relat_1(X0) != sK2 | ~r2_relset_1(X1,X2,k5_relat_1(X0,sK4),k6_partfun1(k2_relat_1(sK4))) | ~m1_subset_1(k5_relat_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK4) = X0 | ~m1_subset_1(k6_partfun1(k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 2.00/0.66    inference(superposition,[],[f453,f264])).
% 2.00/0.66  fof(f264,plain,(
% 2.00/0.66    sK2 = k1_relat_1(sK4)),
% 2.00/0.66    inference(backward_demodulation,[],[f199,f252])).
% 2.00/0.66  fof(f252,plain,(
% 2.00/0.66    sK2 = k1_relset_1(sK2,sK1,sK4)),
% 2.00/0.66    inference(subsumption_resolution,[],[f251,f75])).
% 2.00/0.66  fof(f251,plain,(
% 2.00/0.66    k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,sK4)),
% 2.00/0.66    inference(subsumption_resolution,[],[f247,f70])).
% 2.00/0.66  fof(f247,plain,(
% 2.00/0.66    ~v1_funct_2(sK4,sK2,sK1) | k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,sK4)),
% 2.00/0.66    inference(resolution,[],[f100,f148])).
% 2.00/0.66  fof(f148,plain,(
% 2.00/0.66    sP0(sK2,sK4,sK1)),
% 2.00/0.66    inference(resolution,[],[f104,f71])).
% 2.00/0.66  fof(f199,plain,(
% 2.00/0.66    k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4)),
% 2.00/0.66    inference(resolution,[],[f97,f71])).
% 2.00/0.66  fof(f453,plain,(
% 2.00/0.66    ( ! [X2,X0,X3,X1] : (k1_relat_1(X0) != k2_relat_1(X3) | ~r2_relset_1(X1,X2,k5_relat_1(X3,X0),k6_partfun1(k2_relat_1(X0))) | ~m1_subset_1(k5_relat_1(X3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(X0) = X3 | ~m1_subset_1(k6_partfun1(k2_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(X0) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/0.66    inference(extensionality_resolution,[],[f112,f122])).
% 2.00/0.66  fof(f122,plain,(
% 2.00/0.66    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/0.66    inference(definition_unfolding,[],[f91,f78])).
% 2.00/0.66  fof(f91,plain,(
% 2.00/0.66    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f37])).
% 2.00/0.66  fof(f37,plain,(
% 2.00/0.66    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.00/0.66    inference(flattening,[],[f36])).
% 2.00/0.66  fof(f36,plain,(
% 2.00/0.66    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.00/0.66    inference(ennf_transformation,[],[f10])).
% 2.00/0.66  fof(f10,axiom,(
% 2.00/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 2.00/0.66  fof(f1009,plain,(
% 2.00/0.66    ~spl5_8),
% 2.00/0.66    inference(avatar_contradiction_clause,[],[f1008])).
% 2.00/0.66  fof(f1008,plain,(
% 2.00/0.66    $false | ~spl5_8),
% 2.00/0.66    inference(subsumption_resolution,[],[f1001,f118])).
% 2.00/0.66  fof(f118,plain,(
% 2.00/0.66    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.00/0.66    inference(definition_unfolding,[],[f81,f78])).
% 2.00/0.66  fof(f81,plain,(
% 2.00/0.66    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.00/0.66    inference(cnf_transformation,[],[f6])).
% 2.00/0.66  fof(f6,axiom,(
% 2.00/0.66    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.00/0.66  fof(f1001,plain,(
% 2.00/0.66    ~v2_funct_1(k6_partfun1(sK1)) | ~spl5_8),
% 2.00/0.66    inference(backward_demodulation,[],[f529,f1000])).
% 2.00/0.66  fof(f529,plain,(
% 2.00/0.66    ~v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_8),
% 2.00/0.66    inference(subsumption_resolution,[],[f528,f66])).
% 2.00/0.66  fof(f528,plain,(
% 2.00/0.66    ~v1_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_8),
% 2.00/0.66    inference(subsumption_resolution,[],[f522,f137])).
% 2.00/0.66  fof(f522,plain,(
% 2.00/0.66    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_8),
% 2.00/0.66    inference(trivial_inequality_removal,[],[f520])).
% 2.00/0.66  fof(f520,plain,(
% 2.00/0.66    sK2 != sK2 | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_8),
% 2.00/0.66    inference(superposition,[],[f327,f516])).
% 2.00/0.66  fof(f327,plain,(
% 2.00/0.66    ( ! [X2] : (sK2 != k2_relat_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(k5_relat_1(X2,sK4))) ) | ~spl5_8),
% 2.00/0.66    inference(avatar_component_clause,[],[f326])).
% 2.00/0.66  fof(f326,plain,(
% 2.00/0.66    spl5_8 <=> ! [X2] : (sK2 != k2_relat_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(k5_relat_1(X2,sK4)))),
% 2.00/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.00/0.66  fof(f328,plain,(
% 2.00/0.66    spl5_7 | spl5_8),
% 2.00/0.66    inference(avatar_split_clause,[],[f320,f326,f322])).
% 2.00/0.66  fof(f320,plain,(
% 2.00/0.66    ( ! [X2] : (sK2 != k2_relat_1(X2) | v2_funct_1(sK4) | ~v2_funct_1(k5_relat_1(X2,sK4)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.00/0.66    inference(subsumption_resolution,[],[f319,f138])).
% 2.00/0.66  fof(f319,plain,(
% 2.00/0.66    ( ! [X2] : (sK2 != k2_relat_1(X2) | v2_funct_1(sK4) | ~v2_funct_1(k5_relat_1(X2,sK4)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK4)) )),
% 2.00/0.66    inference(subsumption_resolution,[],[f316,f69])).
% 2.00/0.66  fof(f316,plain,(
% 2.00/0.66    ( ! [X2] : (sK2 != k2_relat_1(X2) | v2_funct_1(sK4) | ~v2_funct_1(k5_relat_1(X2,sK4)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 2.00/0.66    inference(superposition,[],[f93,f264])).
% 2.00/0.66  fof(f93,plain,(
% 2.00/0.66    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f39])).
% 2.00/0.66  fof(f39,plain,(
% 2.00/0.66    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.00/0.66    inference(flattening,[],[f38])).
% 2.00/0.66  fof(f38,plain,(
% 2.00/0.66    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.00/0.66    inference(ennf_transformation,[],[f7])).
% 2.00/0.66  fof(f7,axiom,(
% 2.00/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 2.00/0.66  % SZS output end Proof for theBenchmark
% 2.00/0.66  % (26418)------------------------------
% 2.00/0.66  % (26418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.66  % (26418)Termination reason: Refutation
% 2.20/0.66  
% 2.20/0.66  % (26418)Memory used [KB]: 12409
% 2.20/0.66  % (26418)Time elapsed: 0.228 s
% 2.20/0.66  % (26418)------------------------------
% 2.20/0.66  % (26418)------------------------------
% 2.20/0.66  % (26411)Success in time 0.295 s
%------------------------------------------------------------------------------
