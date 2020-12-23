%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:37 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 693 expanded)
%              Number of leaves         :   21 ( 219 expanded)
%              Depth                    :   24
%              Number of atoms          :  710 (7044 expanded)
%              Number of equality atoms :  215 (2425 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f926,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f162,f234,f305,f824,f851,f925])).

fof(f925,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f924])).

fof(f924,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f889,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f889,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f886,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f886,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f885,f165])).

fof(f165,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f163,f80])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f73,f68])).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f73,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f163,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl4_2 ),
    inference(superposition,[],[f80,f150])).

fof(f150,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_2
  <=> k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f885,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f884,f136])).

fof(f136,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f103,f97])).

fof(f97,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(global_subsumption,[],[f45,f96])).

fof(f96,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f44,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f44,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f45,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f884,plain,
    ( k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f883])).

fof(f883,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f882,f135])).

fof(f135,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f98,f94])).

fof(f94,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f42,f93])).

fof(f93,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f92,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f41,f60])).

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f42,f75])).

fof(f882,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f881,f145])).

fof(f145,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f881,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f880,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f880,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f879,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f879,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f878,f48])).

fof(f48,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f878,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f874,f51])).

fof(f51,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f874,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(superposition,[],[f76,f229])).

fof(f229,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl4_3
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f851,plain,
    ( spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f850])).

fof(f850,plain,
    ( $false
    | spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f846,f339])).

fof(f339,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl4_8
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f846,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f845,f40])).

fof(f845,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f844,f42])).

fof(f844,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f843,f292])).

fof(f292,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl4_5
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f843,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f389,f233])).

fof(f233,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl4_4
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f389,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f70,f387])).

fof(f387,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f386,f122])).

fof(f122,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f121,f40])).

fof(f121,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f120,f41])).

fof(f120,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f119,f42])).

fof(f119,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f48])).

fof(f118,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f112,f50])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f52,f46])).

fof(f46,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f386,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f385,f40])).

fof(f385,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f384,f41])).

fof(f384,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f383,f42])).

fof(f383,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f382,f48])).

fof(f382,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f381])).

fof(f381,plain,
    ( sK1 != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f157,f46])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X2,X1,X0) != X1
      | k1_partfun1(sK0,sK1,X1,X2,sK2,k2_funct_1(X0)) = k5_relat_1(sK2,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X0,X2,X1)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f153,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k2_funct_1(X0))
      | k1_partfun1(sK0,sK1,X1,X2,sK2,k2_funct_1(X0)) = k5_relat_1(sK2,k2_funct_1(X0))
      | k2_relset_1(X2,X1,X0) != X1
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X0,X2,X1)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f101,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f99,f40])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f42,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f824,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f823])).

fof(f823,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f822,f46])).

fof(f822,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl4_8 ),
    inference(subsumption_resolution,[],[f821,f42])).

fof(f821,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl4_8 ),
    inference(resolution,[],[f362,f41])).

fof(f362,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 )
    | spl4_8 ),
    inference(subsumption_resolution,[],[f361,f40])).

fof(f361,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | spl4_8 ),
    inference(subsumption_resolution,[],[f360,f48])).

fof(f360,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v2_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | spl4_8 ),
    inference(resolution,[],[f340,f54])).

fof(f340,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f338])).

fof(f305,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f303,f40])).

fof(f303,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f302,f41])).

fof(f302,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f301,f42])).

fof(f301,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f300,f48])).

fof(f300,plain,
    ( ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f299,f46])).

fof(f299,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(resolution,[],[f293,f56])).

fof(f293,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f291])).

fof(f234,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f214,f231,f227])).

fof(f214,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f212,f213])).

fof(f213,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f202,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f202,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f47,f160])).

fof(f160,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f156,f43])).

fof(f156,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f101,f45])).

fof(f47,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f212,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f211,f40])).

fof(f211,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f210,f42])).

fof(f210,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f209,f43])).

fof(f209,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f204,f45])).

fof(f204,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f70,f160])).

fof(f162,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f152,f42])).

fof(f152,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_1 ),
    inference(resolution,[],[f146,f72])).

fof(f146,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f151,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f142,f148,f144])).

fof(f142,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f91,f127])).

fof(f127,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f126,f40])).

fof(f126,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f124,f42])).

fof(f124,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f123,f48])).

fof(f123,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f111,f50])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f53,f46])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f89,f40])).

fof(f89,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f59,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:31:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (7538)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (7525)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (7534)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.58  % (7517)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.58  % (7522)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.59  % (7536)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.59  % (7529)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.60  % (7518)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.60  % (7527)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.60  % (7543)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.60  % (7514)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.60  % (7515)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.60  % (7512)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.61  % (7544)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.61  % (7523)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.61  % (7535)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.61  % (7542)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.61  % (7541)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.94/0.61  % (7521)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.94/0.62  % (7524)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.94/0.62  % (7531)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.94/0.62  % (7528)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.94/0.62  % (7516)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.94/0.62  % (7520)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.94/0.62  % (7532)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.94/0.62  % (7519)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.94/0.62  % (7540)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.94/0.62  % (7533)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.94/0.63  % (7530)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.94/0.63  % (7537)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.94/0.63  % (7530)Refutation not found, incomplete strategy% (7530)------------------------------
% 1.94/0.63  % (7530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.63  % (7538)Refutation found. Thanks to Tanya!
% 1.94/0.63  % SZS status Theorem for theBenchmark
% 2.04/0.64  % (7530)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.64  
% 2.04/0.64  % (7530)Memory used [KB]: 10746
% 2.04/0.64  % (7530)Time elapsed: 0.192 s
% 2.04/0.64  % (7530)------------------------------
% 2.04/0.64  % (7530)------------------------------
% 2.04/0.65  % SZS output start Proof for theBenchmark
% 2.04/0.65  fof(f926,plain,(
% 2.04/0.65    $false),
% 2.04/0.65    inference(avatar_sat_refutation,[],[f151,f162,f234,f305,f824,f851,f925])).
% 2.04/0.65  fof(f925,plain,(
% 2.04/0.65    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 2.04/0.65    inference(avatar_contradiction_clause,[],[f924])).
% 2.04/0.65  fof(f924,plain,(
% 2.04/0.65    $false | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.04/0.65    inference(resolution,[],[f889,f45])).
% 2.04/0.65  fof(f45,plain,(
% 2.04/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.04/0.65    inference(cnf_transformation,[],[f37])).
% 2.04/0.65  fof(f37,plain,(
% 2.04/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.04/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f36,f35])).
% 2.04/0.65  fof(f35,plain,(
% 2.04/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.04/0.65    introduced(choice_axiom,[])).
% 2.04/0.65  fof(f36,plain,(
% 2.04/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.04/0.65    introduced(choice_axiom,[])).
% 2.04/0.65  fof(f16,plain,(
% 2.04/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.04/0.65    inference(flattening,[],[f15])).
% 2.04/0.65  fof(f15,plain,(
% 2.04/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.04/0.65    inference(ennf_transformation,[],[f14])).
% 2.04/0.65  fof(f14,negated_conjecture,(
% 2.04/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.04/0.65    inference(negated_conjecture,[],[f13])).
% 2.04/0.65  fof(f13,conjecture,(
% 2.04/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.04/0.65  fof(f889,plain,(
% 2.04/0.65    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.04/0.65    inference(resolution,[],[f886,f72])).
% 2.04/0.65  fof(f72,plain,(
% 2.04/0.65    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/0.65    inference(cnf_transformation,[],[f33])).
% 2.04/0.65  fof(f33,plain,(
% 2.04/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/0.65    inference(ennf_transformation,[],[f4])).
% 2.04/0.65  fof(f4,axiom,(
% 2.04/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.04/0.65  fof(f886,plain,(
% 2.04/0.65    ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.04/0.65    inference(subsumption_resolution,[],[f885,f165])).
% 2.04/0.65  fof(f165,plain,(
% 2.04/0.65    sK1 = k2_relat_1(sK2) | ~spl4_2),
% 2.04/0.65    inference(forward_demodulation,[],[f163,f80])).
% 2.04/0.65  fof(f80,plain,(
% 2.04/0.65    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.04/0.65    inference(definition_unfolding,[],[f73,f68])).
% 2.04/0.65  fof(f68,plain,(
% 2.04/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f10])).
% 2.04/0.65  fof(f10,axiom,(
% 2.04/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.04/0.65  fof(f73,plain,(
% 2.04/0.65    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.04/0.65    inference(cnf_transformation,[],[f1])).
% 2.04/0.65  fof(f1,axiom,(
% 2.04/0.65    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.04/0.65  fof(f163,plain,(
% 2.04/0.65    k2_relat_1(sK2) = k1_relat_1(k6_partfun1(sK1)) | ~spl4_2),
% 2.04/0.65    inference(superposition,[],[f80,f150])).
% 2.16/0.65  fof(f150,plain,(
% 2.16/0.65    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) | ~spl4_2),
% 2.16/0.65    inference(avatar_component_clause,[],[f148])).
% 2.16/0.65  fof(f148,plain,(
% 2.16/0.65    spl4_2 <=> k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)),
% 2.16/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.16/0.65  fof(f885,plain,(
% 2.16/0.65    sK1 != k2_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3)),
% 2.16/0.65    inference(forward_demodulation,[],[f884,f136])).
% 2.16/0.65  fof(f136,plain,(
% 2.16/0.65    sK1 = k1_relat_1(sK3)),
% 2.16/0.65    inference(forward_demodulation,[],[f103,f97])).
% 2.16/0.65  fof(f97,plain,(
% 2.16/0.65    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.16/0.65    inference(global_subsumption,[],[f45,f96])).
% 2.16/0.65  fof(f96,plain,(
% 2.16/0.65    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.16/0.65    inference(subsumption_resolution,[],[f95,f49])).
% 2.16/0.65  fof(f49,plain,(
% 2.16/0.65    k1_xboole_0 != sK0),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f95,plain,(
% 2.16/0.65    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.16/0.65    inference(resolution,[],[f44,f60])).
% 2.16/0.65  fof(f60,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.65    inference(cnf_transformation,[],[f38])).
% 2.16/0.65  fof(f38,plain,(
% 2.16/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.65    inference(nnf_transformation,[],[f26])).
% 2.16/0.65  fof(f26,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.65    inference(flattening,[],[f25])).
% 2.16/0.65  fof(f25,plain,(
% 2.16/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.65    inference(ennf_transformation,[],[f7])).
% 2.16/0.65  fof(f7,axiom,(
% 2.16/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.16/0.65  fof(f44,plain,(
% 2.16/0.65    v1_funct_2(sK3,sK1,sK0)),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f103,plain,(
% 2.16/0.65    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 2.16/0.65    inference(resolution,[],[f45,f75])).
% 2.16/0.65  fof(f75,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f34])).
% 2.16/0.65  fof(f34,plain,(
% 2.16/0.65    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.65    inference(ennf_transformation,[],[f5])).
% 2.16/0.65  fof(f5,axiom,(
% 2.16/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.16/0.65  fof(f884,plain,(
% 2.16/0.65    k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3)),
% 2.16/0.65    inference(trivial_inequality_removal,[],[f883])).
% 2.16/0.65  fof(f883,plain,(
% 2.16/0.65    k6_partfun1(sK0) != k6_partfun1(sK0) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3)),
% 2.16/0.65    inference(forward_demodulation,[],[f882,f135])).
% 2.16/0.65  fof(f135,plain,(
% 2.16/0.65    sK0 = k1_relat_1(sK2)),
% 2.16/0.65    inference(forward_demodulation,[],[f98,f94])).
% 2.16/0.65  fof(f94,plain,(
% 2.16/0.65    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.16/0.65    inference(global_subsumption,[],[f42,f93])).
% 2.16/0.65  fof(f93,plain,(
% 2.16/0.65    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.16/0.65    inference(subsumption_resolution,[],[f92,f50])).
% 2.16/0.65  fof(f50,plain,(
% 2.16/0.65    k1_xboole_0 != sK1),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f92,plain,(
% 2.16/0.65    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.16/0.65    inference(resolution,[],[f41,f60])).
% 2.16/0.65  fof(f41,plain,(
% 2.16/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f42,plain,(
% 2.16/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f98,plain,(
% 2.16/0.65    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 2.16/0.65    inference(resolution,[],[f42,f75])).
% 2.16/0.65  fof(f882,plain,(
% 2.16/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_3)),
% 2.16/0.65    inference(subsumption_resolution,[],[f881,f145])).
% 2.16/0.65  fof(f145,plain,(
% 2.16/0.65    v1_relat_1(sK2) | ~spl4_1),
% 2.16/0.65    inference(avatar_component_clause,[],[f144])).
% 2.16/0.65  fof(f144,plain,(
% 2.16/0.65    spl4_1 <=> v1_relat_1(sK2)),
% 2.16/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.16/0.65  fof(f881,plain,(
% 2.16/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_3),
% 2.16/0.65    inference(subsumption_resolution,[],[f880,f40])).
% 2.16/0.65  fof(f40,plain,(
% 2.16/0.65    v1_funct_1(sK2)),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f880,plain,(
% 2.16/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_3),
% 2.16/0.65    inference(subsumption_resolution,[],[f879,f43])).
% 2.16/0.65  fof(f43,plain,(
% 2.16/0.65    v1_funct_1(sK3)),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f879,plain,(
% 2.16/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_3),
% 2.16/0.65    inference(subsumption_resolution,[],[f878,f48])).
% 2.16/0.65  fof(f48,plain,(
% 2.16/0.65    v2_funct_1(sK2)),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f878,plain,(
% 2.16/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_3),
% 2.16/0.65    inference(subsumption_resolution,[],[f874,f51])).
% 2.16/0.65  fof(f51,plain,(
% 2.16/0.65    k2_funct_1(sK2) != sK3),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f874,plain,(
% 2.16/0.65    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_3),
% 2.16/0.65    inference(superposition,[],[f76,f229])).
% 2.16/0.65  fof(f229,plain,(
% 2.16/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_3),
% 2.16/0.65    inference(avatar_component_clause,[],[f227])).
% 2.16/0.65  fof(f227,plain,(
% 2.16/0.65    spl4_3 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.16/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.16/0.65  fof(f76,plain,(
% 2.16/0.65    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.65    inference(definition_unfolding,[],[f57,f68])).
% 2.16/0.65  fof(f57,plain,(
% 2.16/0.65    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f22])).
% 2.16/0.65  fof(f22,plain,(
% 2.16/0.65    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/0.65    inference(flattening,[],[f21])).
% 2.16/0.65  fof(f21,plain,(
% 2.16/0.65    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/0.65    inference(ennf_transformation,[],[f3])).
% 2.16/0.65  fof(f3,axiom,(
% 2.16/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 2.16/0.65  fof(f851,plain,(
% 2.16/0.65    spl4_4 | ~spl4_5 | ~spl4_8),
% 2.16/0.65    inference(avatar_contradiction_clause,[],[f850])).
% 2.16/0.65  fof(f850,plain,(
% 2.16/0.65    $false | (spl4_4 | ~spl4_5 | ~spl4_8)),
% 2.16/0.65    inference(subsumption_resolution,[],[f846,f339])).
% 2.16/0.65  fof(f339,plain,(
% 2.16/0.65    v1_funct_1(k2_funct_1(sK2)) | ~spl4_8),
% 2.16/0.65    inference(avatar_component_clause,[],[f338])).
% 2.16/0.65  fof(f338,plain,(
% 2.16/0.65    spl4_8 <=> v1_funct_1(k2_funct_1(sK2))),
% 2.16/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.16/0.65  fof(f846,plain,(
% 2.16/0.65    ~v1_funct_1(k2_funct_1(sK2)) | (spl4_4 | ~spl4_5)),
% 2.16/0.65    inference(subsumption_resolution,[],[f845,f40])).
% 2.16/0.65  fof(f845,plain,(
% 2.16/0.65    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_4 | ~spl4_5)),
% 2.16/0.65    inference(subsumption_resolution,[],[f844,f42])).
% 2.16/0.65  fof(f844,plain,(
% 2.16/0.65    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (spl4_4 | ~spl4_5)),
% 2.16/0.65    inference(subsumption_resolution,[],[f843,f292])).
% 2.16/0.65  fof(f292,plain,(
% 2.16/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_5),
% 2.16/0.65    inference(avatar_component_clause,[],[f291])).
% 2.16/0.65  fof(f291,plain,(
% 2.16/0.65    spl4_5 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.16/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.16/0.65  fof(f843,plain,(
% 2.16/0.65    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_4),
% 2.16/0.65    inference(subsumption_resolution,[],[f389,f233])).
% 2.16/0.65  fof(f233,plain,(
% 2.16/0.65    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_4),
% 2.16/0.65    inference(avatar_component_clause,[],[f231])).
% 2.16/0.65  fof(f231,plain,(
% 2.16/0.65    spl4_4 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.16/0.65  fof(f389,plain,(
% 2.16/0.65    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(superposition,[],[f70,f387])).
% 2.16/0.65  fof(f387,plain,(
% 2.16/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))),
% 2.16/0.65    inference(forward_demodulation,[],[f386,f122])).
% 2.16/0.65  fof(f122,plain,(
% 2.16/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.16/0.65    inference(subsumption_resolution,[],[f121,f40])).
% 2.16/0.65  fof(f121,plain,(
% 2.16/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f120,f41])).
% 2.16/0.65  fof(f120,plain,(
% 2.16/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f119,f42])).
% 2.16/0.65  fof(f119,plain,(
% 2.16/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f118,f48])).
% 2.16/0.65  fof(f118,plain,(
% 2.16/0.65    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f112,f50])).
% 2.16/0.65  fof(f112,plain,(
% 2.16/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(trivial_inequality_removal,[],[f109])).
% 2.16/0.65  fof(f109,plain,(
% 2.16/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(superposition,[],[f52,f46])).
% 2.16/0.65  fof(f46,plain,(
% 2.16/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f52,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f18])).
% 2.16/0.65  fof(f18,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.16/0.65    inference(flattening,[],[f17])).
% 2.16/0.65  fof(f17,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.16/0.65    inference(ennf_transformation,[],[f12])).
% 2.16/0.65  fof(f12,axiom,(
% 2.16/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.16/0.65  fof(f386,plain,(
% 2.16/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))),
% 2.16/0.65    inference(subsumption_resolution,[],[f385,f40])).
% 2.16/0.65  fof(f385,plain,(
% 2.16/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f384,f41])).
% 2.16/0.65  fof(f384,plain,(
% 2.16/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f383,f42])).
% 2.16/0.65  fof(f383,plain,(
% 2.16/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f382,f48])).
% 2.16/0.65  fof(f382,plain,(
% 2.16/0.65    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(trivial_inequality_removal,[],[f381])).
% 2.16/0.65  fof(f381,plain,(
% 2.16/0.65    sK1 != sK1 | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(superposition,[],[f157,f46])).
% 2.16/0.65  fof(f157,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X2,X1,X0) != X1 | k1_partfun1(sK0,sK1,X1,X2,sK2,k2_funct_1(X0)) = k5_relat_1(sK2,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X0,X2,X1) | ~v1_funct_1(X0)) )),
% 2.16/0.65    inference(subsumption_resolution,[],[f153,f54])).
% 2.16/0.65  fof(f54,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f20])).
% 2.16/0.65  fof(f20,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.16/0.65    inference(flattening,[],[f19])).
% 2.16/0.65  fof(f19,plain,(
% 2.16/0.65    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.16/0.65    inference(ennf_transformation,[],[f11])).
% 2.16/0.65  fof(f11,axiom,(
% 2.16/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.16/0.65  fof(f153,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~v1_funct_1(k2_funct_1(X0)) | k1_partfun1(sK0,sK1,X1,X2,sK2,k2_funct_1(X0)) = k5_relat_1(sK2,k2_funct_1(X0)) | k2_relset_1(X2,X1,X0) != X1 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X0,X2,X1) | ~v1_funct_1(X0)) )),
% 2.16/0.65    inference(resolution,[],[f101,f56])).
% 2.16/0.65  fof(f56,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f20])).
% 2.16/0.65  fof(f101,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 2.16/0.65    inference(subsumption_resolution,[],[f99,f40])).
% 2.16/0.65  fof(f99,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 2.16/0.65    inference(resolution,[],[f42,f71])).
% 2.16/0.65  fof(f71,plain,(
% 2.16/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f32])).
% 2.16/0.65  fof(f32,plain,(
% 2.16/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.16/0.65    inference(flattening,[],[f31])).
% 2.16/0.65  fof(f31,plain,(
% 2.16/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.16/0.65    inference(ennf_transformation,[],[f9])).
% 2.16/0.65  fof(f9,axiom,(
% 2.16/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.16/0.65  fof(f70,plain,(
% 2.16/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f30])).
% 2.16/0.65  fof(f30,plain,(
% 2.16/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.16/0.65    inference(flattening,[],[f29])).
% 2.16/0.65  fof(f29,plain,(
% 2.16/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.16/0.65    inference(ennf_transformation,[],[f8])).
% 2.16/0.65  fof(f8,axiom,(
% 2.16/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.16/0.65  fof(f824,plain,(
% 2.16/0.65    spl4_8),
% 2.16/0.65    inference(avatar_contradiction_clause,[],[f823])).
% 2.16/0.65  fof(f823,plain,(
% 2.16/0.65    $false | spl4_8),
% 2.16/0.65    inference(subsumption_resolution,[],[f822,f46])).
% 2.16/0.65  fof(f822,plain,(
% 2.16/0.65    sK1 != k2_relset_1(sK0,sK1,sK2) | spl4_8),
% 2.16/0.65    inference(subsumption_resolution,[],[f821,f42])).
% 2.16/0.65  fof(f821,plain,(
% 2.16/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | spl4_8),
% 2.16/0.65    inference(resolution,[],[f362,f41])).
% 2.16/0.65  fof(f362,plain,(
% 2.16/0.65    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1) ) | spl4_8),
% 2.16/0.65    inference(subsumption_resolution,[],[f361,f40])).
% 2.16/0.65  fof(f361,plain,(
% 2.16/0.65    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | spl4_8),
% 2.16/0.65    inference(subsumption_resolution,[],[f360,f48])).
% 2.16/0.65  fof(f360,plain,(
% 2.16/0.65    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | spl4_8),
% 2.16/0.65    inference(resolution,[],[f340,f54])).
% 2.16/0.65  fof(f340,plain,(
% 2.16/0.65    ~v1_funct_1(k2_funct_1(sK2)) | spl4_8),
% 2.16/0.65    inference(avatar_component_clause,[],[f338])).
% 2.16/0.65  fof(f305,plain,(
% 2.16/0.65    spl4_5),
% 2.16/0.65    inference(avatar_contradiction_clause,[],[f304])).
% 2.16/0.65  fof(f304,plain,(
% 2.16/0.65    $false | spl4_5),
% 2.16/0.65    inference(subsumption_resolution,[],[f303,f40])).
% 2.16/0.65  fof(f303,plain,(
% 2.16/0.65    ~v1_funct_1(sK2) | spl4_5),
% 2.16/0.65    inference(subsumption_resolution,[],[f302,f41])).
% 2.16/0.65  fof(f302,plain,(
% 2.16/0.65    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_5),
% 2.16/0.65    inference(subsumption_resolution,[],[f301,f42])).
% 2.16/0.65  fof(f301,plain,(
% 2.16/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_5),
% 2.16/0.65    inference(subsumption_resolution,[],[f300,f48])).
% 2.16/0.65  fof(f300,plain,(
% 2.16/0.65    ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_5),
% 2.16/0.65    inference(subsumption_resolution,[],[f299,f46])).
% 2.16/0.65  fof(f299,plain,(
% 2.16/0.65    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_5),
% 2.16/0.65    inference(resolution,[],[f293,f56])).
% 2.16/0.65  fof(f293,plain,(
% 2.16/0.65    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_5),
% 2.16/0.65    inference(avatar_component_clause,[],[f291])).
% 2.16/0.65  fof(f234,plain,(
% 2.16/0.65    spl4_3 | ~spl4_4),
% 2.16/0.65    inference(avatar_split_clause,[],[f214,f231,f227])).
% 2.16/0.65  fof(f214,plain,(
% 2.16/0.65    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.16/0.65    inference(global_subsumption,[],[f212,f213])).
% 2.16/0.65  fof(f213,plain,(
% 2.16/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.65    inference(resolution,[],[f202,f66])).
% 2.16/0.65  fof(f66,plain,(
% 2.16/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.65    inference(cnf_transformation,[],[f39])).
% 2.16/0.65  fof(f39,plain,(
% 2.16/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.65    inference(nnf_transformation,[],[f28])).
% 2.16/0.65  fof(f28,plain,(
% 2.16/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.65    inference(flattening,[],[f27])).
% 2.16/0.65  fof(f27,plain,(
% 2.16/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.16/0.65    inference(ennf_transformation,[],[f6])).
% 2.16/0.65  fof(f6,axiom,(
% 2.16/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.16/0.65  fof(f202,plain,(
% 2.16/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.16/0.65    inference(backward_demodulation,[],[f47,f160])).
% 2.16/0.65  fof(f160,plain,(
% 2.16/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.16/0.65    inference(subsumption_resolution,[],[f156,f43])).
% 2.16/0.65  fof(f156,plain,(
% 2.16/0.65    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.16/0.65    inference(resolution,[],[f101,f45])).
% 2.16/0.65  fof(f47,plain,(
% 2.16/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.16/0.65    inference(cnf_transformation,[],[f37])).
% 2.16/0.65  fof(f212,plain,(
% 2.16/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.65    inference(subsumption_resolution,[],[f211,f40])).
% 2.16/0.65  fof(f211,plain,(
% 2.16/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f210,f42])).
% 2.16/0.65  fof(f210,plain,(
% 2.16/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f209,f43])).
% 2.16/0.65  fof(f209,plain,(
% 2.16/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f204,f45])).
% 2.16/0.65  fof(f204,plain,(
% 2.16/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(superposition,[],[f70,f160])).
% 2.16/0.65  fof(f162,plain,(
% 2.16/0.65    spl4_1),
% 2.16/0.65    inference(avatar_contradiction_clause,[],[f161])).
% 2.16/0.65  fof(f161,plain,(
% 2.16/0.65    $false | spl4_1),
% 2.16/0.65    inference(resolution,[],[f152,f42])).
% 2.16/0.65  fof(f152,plain,(
% 2.16/0.65    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_1),
% 2.16/0.65    inference(resolution,[],[f146,f72])).
% 2.16/0.65  fof(f146,plain,(
% 2.16/0.65    ~v1_relat_1(sK2) | spl4_1),
% 2.16/0.65    inference(avatar_component_clause,[],[f144])).
% 2.16/0.65  fof(f151,plain,(
% 2.16/0.65    ~spl4_1 | spl4_2),
% 2.16/0.65    inference(avatar_split_clause,[],[f142,f148,f144])).
% 2.16/0.65  fof(f142,plain,(
% 2.16/0.65    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) | ~v1_relat_1(sK2)),
% 2.16/0.65    inference(forward_demodulation,[],[f91,f127])).
% 2.16/0.65  fof(f127,plain,(
% 2.16/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.16/0.65    inference(subsumption_resolution,[],[f126,f40])).
% 2.16/0.65  fof(f126,plain,(
% 2.16/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f125,f41])).
% 2.16/0.65  fof(f125,plain,(
% 2.16/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f124,f42])).
% 2.16/0.65  fof(f124,plain,(
% 2.16/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f123,f48])).
% 2.16/0.65  fof(f123,plain,(
% 2.16/0.65    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f111,f50])).
% 2.16/0.65  fof(f111,plain,(
% 2.16/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(trivial_inequality_removal,[],[f110])).
% 2.16/0.65  fof(f110,plain,(
% 2.16/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.16/0.65    inference(superposition,[],[f53,f46])).
% 2.16/0.65  fof(f53,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f18])).
% 2.16/0.65  fof(f91,plain,(
% 2.16/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.16/0.65    inference(subsumption_resolution,[],[f89,f40])).
% 2.16/0.65  fof(f89,plain,(
% 2.16/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.16/0.65    inference(resolution,[],[f48,f77])).
% 2.16/0.65  fof(f77,plain,(
% 2.16/0.65    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.65    inference(definition_unfolding,[],[f59,f68])).
% 2.16/0.65  fof(f59,plain,(
% 2.16/0.65    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f24])).
% 2.16/0.65  fof(f24,plain,(
% 2.16/0.65    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/0.65    inference(flattening,[],[f23])).
% 2.16/0.65  fof(f23,plain,(
% 2.16/0.65    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/0.65    inference(ennf_transformation,[],[f2])).
% 2.16/0.65  fof(f2,axiom,(
% 2.16/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.16/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.16/0.65  % SZS output end Proof for theBenchmark
% 2.16/0.65  % (7538)------------------------------
% 2.16/0.65  % (7538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.65  % (7538)Termination reason: Refutation
% 2.16/0.65  
% 2.16/0.65  % (7538)Memory used [KB]: 11385
% 2.16/0.65  % (7538)Time elapsed: 0.186 s
% 2.16/0.65  % (7538)------------------------------
% 2.16/0.65  % (7538)------------------------------
% 2.16/0.65  % (7506)Success in time 0.285 s
%------------------------------------------------------------------------------
