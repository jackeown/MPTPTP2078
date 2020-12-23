%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 638 expanded)
%              Number of leaves         :   28 ( 203 expanded)
%              Depth                    :   22
%              Number of atoms          :  589 (4883 expanded)
%              Number of equality atoms :  146 (1495 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f898,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f126,f138,f150,f159,f180,f214,f232,f756,f897])).

fof(f897,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f896])).

fof(f896,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f895,f241])).

fof(f241,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f61,f153])).

fof(f153,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f54,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK3)
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK1 != k2_relset_1(sK0,sK1,sK3)
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X4] :
        ( sK1 != k2_relset_1(sK0,sK1,sK3)
        & k1_xboole_0 != sK2
        & v2_funct_1(X4)
        & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK3)
      & k1_xboole_0 != sK2
      & v2_funct_1(sK4)
      & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f61,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f895,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f894,f769])).

fof(f769,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(backward_demodulation,[],[f543,f213])).

fof(f213,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl5_15
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f543,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f541,f255])).

fof(f255,plain,
    ( sK1 = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f137,f242])).

fof(f242,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f173,f182])).

fof(f182,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f181,f60])).

fof(f60,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f47])).

fof(f181,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f176,f56])).

fof(f56,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f176,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f173,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f57,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f137,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_7
  <=> k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f541,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f188,f110])).

fof(f110,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f115,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f115,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_4
  <=> v1_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f894,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f506,f819])).

fof(f819,plain,
    ( sK2 = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f384,f648])).

fof(f648,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f634,f438])).

fof(f438,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f58,f346])).

fof(f346,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f343,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f343,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f183,f54])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f177,f55])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f57,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f58,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f634,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f443,f79])).

fof(f443,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f442,f52])).

fof(f442,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f441,f54])).

fof(f441,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f440,f55])).

fof(f440,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f439,f57])).

fof(f439,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f89,f346])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f384,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f186,f100])).

fof(f100,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f110,f63])).

fof(f506,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3)))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(resolution,[],[f505,f190])).

fof(f190,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f189,f100])).

fof(f189,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f154,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f154,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f54,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f505,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f248,f125])).

fof(f125,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_5
  <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 )
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f247,f115])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f244,f221])).

fof(f221,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl5_16
  <=> v1_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ v1_funct_1(k2_funct_1(sK4))
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_9 ),
    inference(superposition,[],[f73,f243])).

fof(f243,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f149,f242])).

fof(f149,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_9
  <=> k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f756,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | spl5_14 ),
    inference(subsumption_resolution,[],[f754,f100])).

fof(f754,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_3
    | spl5_14 ),
    inference(subsumption_resolution,[],[f753,f110])).

fof(f753,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | spl5_14 ),
    inference(subsumption_resolution,[],[f749,f209])).

fof(f209,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK4))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_14
  <=> r1_tarski(sK2,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f749,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f62,f648])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f232,plain,
    ( ~ spl5_3
    | spl5_16 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl5_3
    | spl5_16 ),
    inference(subsumption_resolution,[],[f230,f110])).

fof(f230,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_16 ),
    inference(subsumption_resolution,[],[f229,f55])).

fof(f229,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_16 ),
    inference(resolution,[],[f222,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f222,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f220])).

fof(f214,plain,
    ( ~ spl5_14
    | spl5_15
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f205,f109,f211,f207])).

fof(f205,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ spl5_3 ),
    inference(resolution,[],[f192,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f192,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f191,f110])).

fof(f191,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f175,f70])).

fof(f175,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f57,f80])).

fof(f180,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f172,f111])).

fof(f111,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f172,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f57,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f159,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f151,f101])).

fof(f101,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f151,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f77])).

fof(f150,plain,
    ( ~ spl5_3
    | spl5_9 ),
    inference(avatar_split_clause,[],[f145,f147,f109])).

fof(f145,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f121,f55])).

fof(f121,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f59,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f59,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f138,plain,
    ( ~ spl5_3
    | spl5_7 ),
    inference(avatar_split_clause,[],[f133,f135,f109])).

fof(f133,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f119,f55])).

fof(f119,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f59,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f126,plain,
    ( ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f122,f124,f109])).

fof(f122,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f117,f55])).

fof(f117,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f59,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f116,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f107,f113,f109])).

fof(f107,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f55,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (6150)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (6165)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (6148)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (6149)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (6167)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (6159)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (6158)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (6145)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (6164)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (6169)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (6155)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (6157)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (6146)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (6161)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (6153)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (6160)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (6168)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (6147)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (6152)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (6156)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (6166)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (6163)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (6151)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (6146)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f898,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f116,f126,f138,f150,f159,f180,f214,f232,f756,f897])).
% 0.20/0.55  fof(f897,plain,(
% 0.20/0.55    ~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_15 | ~spl5_16),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f896])).
% 0.20/0.55  fof(f896,plain,(
% 0.20/0.55    $false | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_15 | ~spl5_16)),
% 0.20/0.55    inference(subsumption_resolution,[],[f895,f241])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    sK1 != k2_relat_1(sK3)),
% 0.20/0.55    inference(superposition,[],[f61,f153])).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.20/0.55    inference(resolution,[],[f54,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f46,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.20/0.55    inference(negated_conjecture,[],[f17])).
% 0.20/0.55  fof(f17,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f895,plain,(
% 0.20/0.55    sK1 = k2_relat_1(sK3) | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_15 | ~spl5_16)),
% 0.20/0.55    inference(forward_demodulation,[],[f894,f769])).
% 0.20/0.55  fof(f769,plain,(
% 0.20/0.55    sK1 = k9_relat_1(k2_funct_1(sK4),sK2) | (~spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_15)),
% 0.20/0.55    inference(backward_demodulation,[],[f543,f213])).
% 0.20/0.55  fof(f213,plain,(
% 0.20/0.55    sK2 = k2_relat_1(sK4) | ~spl5_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f211])).
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    spl5_15 <=> sK2 = k2_relat_1(sK4)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.55  fof(f543,plain,(
% 0.20/0.55    sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) | (~spl5_3 | ~spl5_4 | ~spl5_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f541,f255])).
% 0.20/0.55  fof(f255,plain,(
% 0.20/0.55    sK1 = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) | ~spl5_7),
% 0.20/0.55    inference(forward_demodulation,[],[f137,f242])).
% 0.20/0.55  fof(f242,plain,(
% 0.20/0.55    sK1 = k1_relat_1(sK4)),
% 0.20/0.55    inference(forward_demodulation,[],[f173,f182])).
% 0.20/0.55  fof(f182,plain,(
% 0.20/0.55    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f181,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    k1_xboole_0 != sK2),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f181,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f176,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    v1_funct_2(sK4,sK1,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.20/0.55    inference(resolution,[],[f57,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 0.20/0.55    inference(resolution,[],[f57,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) | ~spl5_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f135])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    spl5_7 <=> k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.55  fof(f541,plain,(
% 0.20/0.55    k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) | (~spl5_3 | ~spl5_4)),
% 0.20/0.55    inference(resolution,[],[f188,f110])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    v1_relat_1(sK4) | ~spl5_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f109])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl5_3 <=> v1_relat_1(sK4)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0))) ) | ~spl5_4),
% 0.20/0.55    inference(resolution,[],[f115,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    v1_relat_1(k2_funct_1(sK4)) | ~spl5_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f113])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    spl5_4 <=> v1_relat_1(k2_funct_1(sK4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.56  fof(f894,plain,(
% 0.20/0.56    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2) | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9 | ~spl5_16)),
% 0.20/0.56    inference(forward_demodulation,[],[f506,f819])).
% 0.20/0.56  fof(f819,plain,(
% 0.20/0.56    sK2 = k9_relat_1(sK4,k2_relat_1(sK3)) | (~spl5_1 | ~spl5_3)),
% 0.20/0.56    inference(forward_demodulation,[],[f384,f648])).
% 0.20/0.56  fof(f648,plain,(
% 0.20/0.56    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.20/0.56    inference(forward_demodulation,[],[f634,f438])).
% 0.20/0.56  fof(f438,plain,(
% 0.20/0.56    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.20/0.56    inference(backward_demodulation,[],[f58,f346])).
% 0.20/0.56  fof(f346,plain,(
% 0.20/0.56    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.20/0.56    inference(subsumption_resolution,[],[f343,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    v1_funct_1(sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f47])).
% 0.20/0.56  fof(f343,plain,(
% 0.20/0.56    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 0.20/0.56    inference(resolution,[],[f183,f54])).
% 0.20/0.56  fof(f183,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(X2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f177,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    v1_funct_1(sK4)),
% 0.20/0.56    inference(cnf_transformation,[],[f47])).
% 0.20/0.56  fof(f177,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.56    inference(resolution,[],[f57,f87])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.56    inference(flattening,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.20/0.57    inference(cnf_transformation,[],[f47])).
% 0.20/0.57  fof(f634,plain,(
% 0.20/0.57    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.20/0.57    inference(resolution,[],[f443,f79])).
% 0.20/0.57  fof(f443,plain,(
% 0.20/0.57    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.57    inference(subsumption_resolution,[],[f442,f52])).
% 0.20/0.57  fof(f442,plain,(
% 0.20/0.57    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f441,f54])).
% 0.20/0.57  fof(f441,plain,(
% 0.20/0.57    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f440,f55])).
% 0.20/0.57  fof(f440,plain,(
% 0.20/0.57    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f439,f57])).
% 0.20/0.57  fof(f439,plain,(
% 0.20/0.57    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.20/0.57    inference(superposition,[],[f89,f346])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.57    inference(flattening,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.57  fof(f384,plain,(
% 0.20/0.57    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) | (~spl5_1 | ~spl5_3)),
% 0.20/0.57    inference(resolution,[],[f186,f100])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    v1_relat_1(sK3) | ~spl5_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f99])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    spl5_1 <=> v1_relat_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.57  fof(f186,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0))) ) | ~spl5_3),
% 0.20/0.57    inference(resolution,[],[f110,f63])).
% 0.20/0.57  fof(f506,plain,(
% 0.20/0.57    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))) | (~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_9 | ~spl5_16)),
% 0.20/0.57    inference(resolution,[],[f505,f190])).
% 0.20/0.57  fof(f190,plain,(
% 0.20/0.57    r1_tarski(k2_relat_1(sK3),sK1) | ~spl5_1),
% 0.20/0.57    inference(subsumption_resolution,[],[f189,f100])).
% 0.20/0.57  fof(f189,plain,(
% 0.20/0.57    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f154,f70])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.57  fof(f154,plain,(
% 0.20/0.57    v5_relat_1(sK3,sK1)),
% 0.20/0.57    inference(resolution,[],[f54,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.57    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.57  fof(f505,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0) ) | (~spl5_4 | ~spl5_5 | ~spl5_9 | ~spl5_16)),
% 0.20/0.57    inference(forward_demodulation,[],[f248,f125])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)) ) | ~spl5_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f124])).
% 0.20/0.57  fof(f124,plain,(
% 0.20/0.57    spl5_5 <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.57  fof(f248,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0) ) | (~spl5_4 | ~spl5_9 | ~spl5_16)),
% 0.20/0.57    inference(subsumption_resolution,[],[f247,f115])).
% 0.20/0.57  fof(f247,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~v1_relat_1(k2_funct_1(sK4))) ) | (~spl5_9 | ~spl5_16)),
% 0.20/0.57    inference(subsumption_resolution,[],[f244,f221])).
% 0.20/0.57  fof(f221,plain,(
% 0.20/0.57    v1_funct_1(k2_funct_1(sK4)) | ~spl5_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f220])).
% 0.20/0.57  fof(f220,plain,(
% 0.20/0.57    spl5_16 <=> v1_funct_1(k2_funct_1(sK4))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.57  fof(f244,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))) ) | ~spl5_9),
% 0.20/0.57    inference(superposition,[],[f73,f243])).
% 0.20/0.57  fof(f243,plain,(
% 0.20/0.57    sK1 = k2_relat_1(k2_funct_1(sK4)) | ~spl5_9),
% 0.20/0.57    inference(backward_demodulation,[],[f149,f242])).
% 0.20/0.57  fof(f149,plain,(
% 0.20/0.57    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~spl5_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f147])).
% 0.20/0.57  fof(f147,plain,(
% 0.20/0.57    spl5_9 <=> k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.57  fof(f756,plain,(
% 0.20/0.57    ~spl5_1 | ~spl5_3 | spl5_14),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f755])).
% 0.20/0.57  fof(f755,plain,(
% 0.20/0.57    $false | (~spl5_1 | ~spl5_3 | spl5_14)),
% 0.20/0.57    inference(subsumption_resolution,[],[f754,f100])).
% 0.20/0.57  fof(f754,plain,(
% 0.20/0.57    ~v1_relat_1(sK3) | (~spl5_3 | spl5_14)),
% 0.20/0.57    inference(subsumption_resolution,[],[f753,f110])).
% 0.20/0.57  fof(f753,plain,(
% 0.20/0.57    ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | spl5_14),
% 0.20/0.57    inference(subsumption_resolution,[],[f749,f209])).
% 0.20/0.57  fof(f209,plain,(
% 0.20/0.57    ~r1_tarski(sK2,k2_relat_1(sK4)) | spl5_14),
% 0.20/0.57    inference(avatar_component_clause,[],[f207])).
% 0.20/0.57  fof(f207,plain,(
% 0.20/0.57    spl5_14 <=> r1_tarski(sK2,k2_relat_1(sK4))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.57  fof(f749,plain,(
% 0.20/0.57    r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(superposition,[],[f62,f648])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.57  fof(f232,plain,(
% 0.20/0.57    ~spl5_3 | spl5_16),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f231])).
% 0.20/0.57  fof(f231,plain,(
% 0.20/0.57    $false | (~spl5_3 | spl5_16)),
% 0.20/0.57    inference(subsumption_resolution,[],[f230,f110])).
% 0.20/0.57  fof(f230,plain,(
% 0.20/0.57    ~v1_relat_1(sK4) | spl5_16),
% 0.20/0.57    inference(subsumption_resolution,[],[f229,f55])).
% 0.20/0.57  fof(f229,plain,(
% 0.20/0.57    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_16),
% 0.20/0.57    inference(resolution,[],[f222,f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.57  fof(f222,plain,(
% 0.20/0.57    ~v1_funct_1(k2_funct_1(sK4)) | spl5_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f220])).
% 0.20/0.57  fof(f214,plain,(
% 0.20/0.57    ~spl5_14 | spl5_15 | ~spl5_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f205,f109,f211,f207])).
% 0.20/0.57  fof(f205,plain,(
% 0.20/0.57    sK2 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~spl5_3),
% 0.20/0.57    inference(resolution,[],[f192,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(flattening,[],[f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f192,plain,(
% 0.20/0.57    r1_tarski(k2_relat_1(sK4),sK2) | ~spl5_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f191,f110])).
% 0.20/0.57  fof(f191,plain,(
% 0.20/0.57    r1_tarski(k2_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f175,f70])).
% 0.20/0.57  fof(f175,plain,(
% 0.20/0.57    v5_relat_1(sK4,sK2)),
% 0.20/0.57    inference(resolution,[],[f57,f80])).
% 0.20/0.57  fof(f180,plain,(
% 0.20/0.57    spl5_3),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f179])).
% 0.20/0.57  fof(f179,plain,(
% 0.20/0.57    $false | spl5_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f172,f111])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    ~v1_relat_1(sK4) | spl5_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f109])).
% 0.20/0.57  fof(f172,plain,(
% 0.20/0.57    v1_relat_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f57,f77])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.57  fof(f159,plain,(
% 0.20/0.57    spl5_1),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.57  fof(f158,plain,(
% 0.20/0.57    $false | spl5_1),
% 0.20/0.57    inference(subsumption_resolution,[],[f151,f101])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    ~v1_relat_1(sK3) | spl5_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f99])).
% 0.20/0.57  fof(f151,plain,(
% 0.20/0.57    v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f54,f77])).
% 0.20/0.57  fof(f150,plain,(
% 0.20/0.57    ~spl5_3 | spl5_9),
% 0.20/0.57    inference(avatar_split_clause,[],[f145,f147,f109])).
% 0.20/0.57  fof(f145,plain,(
% 0.20/0.57    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 0.20/0.57    inference(subsumption_resolution,[],[f121,f55])).
% 0.20/0.57  fof(f121,plain,(
% 0.20/0.57    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f59,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    v2_funct_1(sK4)),
% 0.20/0.57    inference(cnf_transformation,[],[f47])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    ~spl5_3 | spl5_7),
% 0.20/0.57    inference(avatar_split_clause,[],[f133,f135,f109])).
% 0.20/0.57  fof(f133,plain,(
% 0.20/0.57    k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) | ~v1_relat_1(sK4)),
% 0.20/0.57    inference(subsumption_resolution,[],[f119,f55])).
% 0.20/0.57  fof(f119,plain,(
% 0.20/0.57    k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f59,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.57  fof(f126,plain,(
% 0.20/0.57    ~spl5_3 | spl5_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f122,f124,f109])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_relat_1(sK4)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f117,f55])).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 0.20/0.57    inference(resolution,[],[f59,f72])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    ~spl5_3 | spl5_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f107,f113,f109])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f55,f64])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (6146)------------------------------
% 0.20/0.57  % (6146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (6146)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (6146)Memory used [KB]: 11129
% 0.20/0.57  % (6146)Time elapsed: 0.136 s
% 0.20/0.57  % (6146)------------------------------
% 0.20/0.57  % (6146)------------------------------
% 0.20/0.57  % (6144)Success in time 0.215 s
%------------------------------------------------------------------------------
