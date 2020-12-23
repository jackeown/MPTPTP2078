%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:28 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 741 expanded)
%              Number of leaves         :   28 ( 235 expanded)
%              Depth                    :   22
%              Number of atoms          :  606 (5725 expanded)
%              Number of equality atoms :  152 (1778 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f688,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f123,f135,f147,f152,f181,f213,f487,f687])).

fof(f687,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f686])).

fof(f686,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f685,f226])).

fof(f226,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f62,f155])).

fof(f155,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f55,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f47,f46])).

fof(f46,plain,
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

fof(f47,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f62,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f685,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f684,f535])).

fof(f535,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f475,f212])).

fof(f212,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl5_14
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f475,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f472,f328])).

fof(f328,plain,
    ( k2_relat_1(sK4) = k9_relat_1(sK4,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f327,f64])).

fof(f64,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f327,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(sK4))) = k9_relat_1(sK4,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f326,f146])).

fof(f146,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_relat_1(k2_relat_1(sK4))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_7
  <=> k5_relat_1(k2_funct_1(sK4),sK4) = k6_relat_1(k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f326,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK4),sK4)) = k9_relat_1(sK4,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f325,f228])).

fof(f228,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f134,f227])).

fof(f227,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f174,f183])).

fof(f183,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f182,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f182,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f177,f57])).

fof(f57,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f177,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f58,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f41])).

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
    inference(flattening,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f174,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f58,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f134,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_5
  <=> k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f325,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK4),sK4)) = k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f186,f116])).

fof(f116,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_2
  <=> v1_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f111,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f111,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_1
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f472,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f436,f95])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f436,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f233,f151])).

fof(f151,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_8
  <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f232,f116])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f229,f122])).

fof(f122,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_3
  <=> v1_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
        | ~ v1_funct_1(k2_funct_1(sK4))
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_5 ),
    inference(superposition,[],[f77,f228])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f684,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f474,f448])).

fof(f448,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f439,f372])).

fof(f372,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f59,f308])).

fof(f308,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f305,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f305,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f184,f55])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f178,f56])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f58,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f59,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f439,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f377,f83])).

fof(f377,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f376,f53])).

fof(f376,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f375,f55])).

fof(f375,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f374,f56])).

fof(f374,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f373,f58])).

fof(f373,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f93,f308])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f474,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f468,f323])).

fof(f323,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1 ),
    inference(resolution,[],[f186,f153])).

fof(f153,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f468,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f436,f189])).

fof(f189,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f188,f153])).

fof(f188,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f156,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f156,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f55,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f487,plain,
    ( ~ spl5_1
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | ~ spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f485,f153])).

fof(f485,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f484,f111])).

fof(f484,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f480,f208])).

fof(f208,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK4))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl5_13
  <=> r1_tarski(sK2,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f480,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f65,f448])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f213,plain,
    ( ~ spl5_13
    | spl5_14
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f204,f110,f210,f206])).

fof(f204,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ spl5_1 ),
    inference(resolution,[],[f191,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f191,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f190,f111])).

fof(f190,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f176,f74])).

fof(f176,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f58,f84])).

fof(f181,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f173,f112])).

fof(f112,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f173,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f58,f81])).

fof(f152,plain,
    ( ~ spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f148,f150,f110])).

fof(f148,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f107,f56])).

fof(f107,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f60,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f60,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f147,plain,
    ( ~ spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f142,f144,f110])).

fof(f142,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_relat_1(k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f106,f56])).

fof(f106,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_relat_1(k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f60,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f135,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f130,f132,f110])).

fof(f130,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f104,f56])).

fof(f104,plain,
    ( k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f60,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f123,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f118,f120,f110])).

fof(f118,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f60,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f117,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f108,f114,f110])).

fof(f108,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f101,f56])).

fof(f101,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f60,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:50:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (15247)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (15248)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (15251)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (15266)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (15249)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.20/0.52  % (15258)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.20/0.52  % (15267)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.20/0.52  % (15252)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.20/0.52  % (15256)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.20/0.53  % (15250)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.20/0.53  % (15254)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.20/0.53  % (15255)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.20/0.53  % (15259)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.20/0.53  % (15268)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.20/0.53  % (15265)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.20/0.53  % (15272)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.20/0.53  % (15271)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.20/0.53  % (15269)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.20/0.53  % (15270)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.20/0.53  % (15261)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.36/0.54  % (15253)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.36/0.55  % (15263)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.36/0.55  % (15248)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f688,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(avatar_sat_refutation,[],[f117,f123,f135,f147,f152,f181,f213,f487,f687])).
% 1.36/0.55  fof(f687,plain,(
% 1.36/0.55    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_14),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f686])).
% 1.36/0.55  fof(f686,plain,(
% 1.36/0.55    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_14)),
% 1.36/0.55    inference(subsumption_resolution,[],[f685,f226])).
% 1.36/0.55  fof(f226,plain,(
% 1.36/0.55    sK1 != k2_relat_1(sK3)),
% 1.36/0.55    inference(superposition,[],[f62,f155])).
% 1.36/0.55  fof(f155,plain,(
% 1.36/0.55    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.36/0.55    inference(resolution,[],[f55,f83])).
% 1.36/0.55  fof(f83,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f38])).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.55  fof(f55,plain,(
% 1.36/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f48,plain,(
% 1.36/0.55    (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f47,f46])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f47,plain,(
% 1.36/0.55    ? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.36/0.55    inference(flattening,[],[f21])).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.36/0.55    inference(ennf_transformation,[],[f19])).
% 1.36/0.55  fof(f19,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.36/0.55    inference(negated_conjecture,[],[f18])).
% 1.36/0.55  fof(f18,conjecture,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 1.36/0.55  fof(f62,plain,(
% 1.36/0.55    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f685,plain,(
% 1.36/0.55    sK1 = k2_relat_1(sK3) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_14)),
% 1.36/0.55    inference(forward_demodulation,[],[f684,f535])).
% 1.36/0.55  fof(f535,plain,(
% 1.36/0.55    sK1 = k9_relat_1(k2_funct_1(sK4),sK2) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_14)),
% 1.36/0.55    inference(forward_demodulation,[],[f475,f212])).
% 1.36/0.55  fof(f212,plain,(
% 1.36/0.55    sK2 = k2_relat_1(sK4) | ~spl5_14),
% 1.36/0.55    inference(avatar_component_clause,[],[f210])).
% 1.36/0.55  fof(f210,plain,(
% 1.36/0.55    spl5_14 <=> sK2 = k2_relat_1(sK4)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.36/0.55  fof(f475,plain,(
% 1.36/0.55    sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_8)),
% 1.36/0.55    inference(forward_demodulation,[],[f472,f328])).
% 1.36/0.55  fof(f328,plain,(
% 1.36/0.55    k2_relat_1(sK4) = k9_relat_1(sK4,sK1) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_7)),
% 1.36/0.55    inference(forward_demodulation,[],[f327,f64])).
% 1.36/0.55  fof(f64,plain,(
% 1.36/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f5])).
% 1.36/0.55  fof(f5,axiom,(
% 1.36/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.36/0.55  fof(f327,plain,(
% 1.36/0.55    k2_relat_1(k6_relat_1(k2_relat_1(sK4))) = k9_relat_1(sK4,sK1) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_7)),
% 1.36/0.55    inference(forward_demodulation,[],[f326,f146])).
% 1.36/0.55  fof(f146,plain,(
% 1.36/0.55    k5_relat_1(k2_funct_1(sK4),sK4) = k6_relat_1(k2_relat_1(sK4)) | ~spl5_7),
% 1.36/0.55    inference(avatar_component_clause,[],[f144])).
% 1.36/0.55  fof(f144,plain,(
% 1.36/0.55    spl5_7 <=> k5_relat_1(k2_funct_1(sK4),sK4) = k6_relat_1(k2_relat_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.36/0.55  fof(f326,plain,(
% 1.36/0.55    k2_relat_1(k5_relat_1(k2_funct_1(sK4),sK4)) = k9_relat_1(sK4,sK1) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.36/0.55    inference(forward_demodulation,[],[f325,f228])).
% 1.36/0.55  fof(f228,plain,(
% 1.36/0.55    sK1 = k2_relat_1(k2_funct_1(sK4)) | ~spl5_5),
% 1.36/0.55    inference(backward_demodulation,[],[f134,f227])).
% 1.36/0.55  fof(f227,plain,(
% 1.36/0.55    sK1 = k1_relat_1(sK4)),
% 1.36/0.55    inference(forward_demodulation,[],[f174,f183])).
% 1.36/0.55  fof(f183,plain,(
% 1.36/0.55    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f182,f61])).
% 1.36/0.55  fof(f61,plain,(
% 1.36/0.55    k1_xboole_0 != sK2),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f182,plain,(
% 1.36/0.55    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f177,f57])).
% 1.36/0.55  fof(f57,plain,(
% 1.36/0.55    v1_funct_2(sK4,sK1,sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f177,plain,(
% 1.36/0.55    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.36/0.55    inference(resolution,[],[f58,f85])).
% 1.36/0.55  fof(f85,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f52])).
% 1.36/0.55  fof(f52,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(nnf_transformation,[],[f41])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(flattening,[],[f40])).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f15])).
% 1.36/0.55  fof(f15,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f174,plain,(
% 1.36/0.55    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 1.36/0.55    inference(resolution,[],[f58,f82])).
% 1.36/0.55  fof(f82,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.36/0.55  fof(f134,plain,(
% 1.36/0.55    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~spl5_5),
% 1.36/0.55    inference(avatar_component_clause,[],[f132])).
% 1.36/0.55  fof(f132,plain,(
% 1.36/0.55    spl5_5 <=> k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.36/0.55  fof(f325,plain,(
% 1.36/0.55    k2_relat_1(k5_relat_1(k2_funct_1(sK4),sK4)) = k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) | (~spl5_1 | ~spl5_2)),
% 1.36/0.55    inference(resolution,[],[f186,f116])).
% 1.36/0.55  fof(f116,plain,(
% 1.36/0.55    v1_relat_1(k2_funct_1(sK4)) | ~spl5_2),
% 1.36/0.55    inference(avatar_component_clause,[],[f114])).
% 1.36/0.55  fof(f114,plain,(
% 1.36/0.55    spl5_2 <=> v1_relat_1(k2_funct_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.36/0.55  fof(f186,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0))) ) | ~spl5_1),
% 1.36/0.55    inference(resolution,[],[f111,f66])).
% 1.36/0.55  fof(f66,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f24])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.36/0.55  fof(f111,plain,(
% 1.36/0.55    v1_relat_1(sK4) | ~spl5_1),
% 1.36/0.55    inference(avatar_component_clause,[],[f110])).
% 1.36/0.55  fof(f110,plain,(
% 1.36/0.55    spl5_1 <=> v1_relat_1(sK4)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.36/0.55  fof(f472,plain,(
% 1.36/0.55    sK1 = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,sK1)) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.36/0.55    inference(resolution,[],[f436,f95])).
% 1.36/0.55  fof(f95,plain,(
% 1.36/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.55    inference(equality_resolution,[],[f78])).
% 1.36/0.55  fof(f78,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.36/0.55    inference(cnf_transformation,[],[f51])).
% 1.36/0.55  fof(f51,plain,(
% 1.36/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.55    inference(flattening,[],[f50])).
% 1.36/0.55  fof(f50,plain,(
% 1.36/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.55    inference(nnf_transformation,[],[f1])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.55  fof(f436,plain,(
% 1.36/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0) ) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.36/0.55    inference(forward_demodulation,[],[f233,f151])).
% 1.36/0.55  fof(f151,plain,(
% 1.36/0.55    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)) ) | ~spl5_8),
% 1.36/0.55    inference(avatar_component_clause,[],[f150])).
% 1.36/0.55  fof(f150,plain,(
% 1.36/0.55    spl5_8 <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.36/0.55  fof(f233,plain,(
% 1.36/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 1.36/0.55    inference(subsumption_resolution,[],[f232,f116])).
% 1.36/0.55  fof(f232,plain,(
% 1.36/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~v1_relat_1(k2_funct_1(sK4))) ) | (~spl5_3 | ~spl5_5)),
% 1.36/0.55    inference(subsumption_resolution,[],[f229,f122])).
% 1.36/0.55  fof(f122,plain,(
% 1.36/0.55    v1_funct_1(k2_funct_1(sK4)) | ~spl5_3),
% 1.36/0.55    inference(avatar_component_clause,[],[f120])).
% 1.36/0.55  fof(f120,plain,(
% 1.36/0.55    spl5_3 <=> v1_funct_1(k2_funct_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.36/0.55  fof(f229,plain,(
% 1.36/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0 | ~v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))) ) | ~spl5_5),
% 1.36/0.55    inference(superposition,[],[f77,f228])).
% 1.36/0.55  fof(f77,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f35])).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(flattening,[],[f34])).
% 1.36/0.55  fof(f34,plain,(
% 1.36/0.55    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.36/0.55  fof(f684,plain,(
% 1.36/0.55    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.36/0.55    inference(forward_demodulation,[],[f474,f448])).
% 1.36/0.55  fof(f448,plain,(
% 1.36/0.55    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.36/0.55    inference(forward_demodulation,[],[f439,f372])).
% 1.36/0.55  fof(f372,plain,(
% 1.36/0.55    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.36/0.55    inference(backward_demodulation,[],[f59,f308])).
% 1.36/0.55  fof(f308,plain,(
% 1.36/0.55    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f305,f53])).
% 1.36/0.55  fof(f53,plain,(
% 1.36/0.55    v1_funct_1(sK3)),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f305,plain,(
% 1.36/0.55    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 1.36/0.55    inference(resolution,[],[f184,f55])).
% 1.36/0.55  fof(f184,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(X2)) )),
% 1.36/0.55    inference(subsumption_resolution,[],[f178,f56])).
% 1.36/0.55  fof(f56,plain,(
% 1.36/0.55    v1_funct_1(sK4)),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f178,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.36/0.55    inference(resolution,[],[f58,f91])).
% 1.36/0.55  fof(f91,plain,(
% 1.36/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f43])).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.36/0.55    inference(flattening,[],[f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.36/0.55    inference(ennf_transformation,[],[f17])).
% 1.36/0.55  fof(f17,axiom,(
% 1.36/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.36/0.55  fof(f59,plain,(
% 1.36/0.55    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f439,plain,(
% 1.36/0.55    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.36/0.55    inference(resolution,[],[f377,f83])).
% 1.36/0.55  fof(f377,plain,(
% 1.36/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.36/0.55    inference(subsumption_resolution,[],[f376,f53])).
% 1.36/0.55  fof(f376,plain,(
% 1.36/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3)),
% 1.36/0.55    inference(subsumption_resolution,[],[f375,f55])).
% 1.36/0.55  fof(f375,plain,(
% 1.36/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.36/0.55    inference(subsumption_resolution,[],[f374,f56])).
% 1.36/0.55  fof(f374,plain,(
% 1.36/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.36/0.55    inference(subsumption_resolution,[],[f373,f58])).
% 1.36/0.55  fof(f373,plain,(
% 1.36/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.36/0.55    inference(superposition,[],[f93,f308])).
% 1.36/0.55  fof(f93,plain,(
% 1.36/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f45])).
% 1.36/0.55  fof(f45,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.36/0.55    inference(flattening,[],[f44])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.36/0.55    inference(ennf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,axiom,(
% 1.36/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.36/0.55  fof(f474,plain,(
% 1.36/0.55    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.36/0.55    inference(forward_demodulation,[],[f468,f323])).
% 1.36/0.55  fof(f323,plain,(
% 1.36/0.55    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) | ~spl5_1),
% 1.36/0.55    inference(resolution,[],[f186,f153])).
% 1.36/0.55  fof(f153,plain,(
% 1.36/0.55    v1_relat_1(sK3)),
% 1.36/0.55    inference(resolution,[],[f55,f81])).
% 1.36/0.55  fof(f81,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f36])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.55  fof(f468,plain,(
% 1.36/0.55    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 1.36/0.55    inference(resolution,[],[f436,f189])).
% 1.36/0.55  fof(f189,plain,(
% 1.36/0.55    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.36/0.55    inference(subsumption_resolution,[],[f188,f153])).
% 1.36/0.55  fof(f188,plain,(
% 1.36/0.55    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.36/0.55    inference(resolution,[],[f156,f74])).
% 1.36/0.55  fof(f74,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f49,plain,(
% 1.36/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(nnf_transformation,[],[f31])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.36/0.55  fof(f156,plain,(
% 1.36/0.55    v5_relat_1(sK3,sK1)),
% 1.36/0.55    inference(resolution,[],[f55,f84])).
% 1.36/0.55  fof(f84,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f39])).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.36/0.55    inference(pure_predicate_removal,[],[f12])).
% 1.36/0.55  fof(f12,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.55  fof(f487,plain,(
% 1.36/0.55    ~spl5_1 | spl5_13),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f486])).
% 1.36/0.55  fof(f486,plain,(
% 1.36/0.55    $false | (~spl5_1 | spl5_13)),
% 1.36/0.55    inference(subsumption_resolution,[],[f485,f153])).
% 1.36/0.55  fof(f485,plain,(
% 1.36/0.55    ~v1_relat_1(sK3) | (~spl5_1 | spl5_13)),
% 1.36/0.55    inference(subsumption_resolution,[],[f484,f111])).
% 1.36/0.55  fof(f484,plain,(
% 1.36/0.55    ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | spl5_13),
% 1.36/0.55    inference(subsumption_resolution,[],[f480,f208])).
% 1.36/0.55  fof(f208,plain,(
% 1.36/0.55    ~r1_tarski(sK2,k2_relat_1(sK4)) | spl5_13),
% 1.36/0.55    inference(avatar_component_clause,[],[f206])).
% 1.36/0.55  fof(f206,plain,(
% 1.36/0.55    spl5_13 <=> r1_tarski(sK2,k2_relat_1(sK4))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.36/0.55  fof(f480,plain,(
% 1.36/0.55    r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 1.36/0.55    inference(superposition,[],[f65,f448])).
% 1.36/0.55  fof(f65,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f23])).
% 1.36/0.55  fof(f23,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.36/0.55  fof(f213,plain,(
% 1.36/0.55    ~spl5_13 | spl5_14 | ~spl5_1),
% 1.36/0.55    inference(avatar_split_clause,[],[f204,f110,f210,f206])).
% 1.36/0.55  fof(f204,plain,(
% 1.36/0.55    sK2 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~spl5_1),
% 1.36/0.55    inference(resolution,[],[f191,f80])).
% 1.36/0.55  fof(f80,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f51])).
% 1.36/0.55  fof(f191,plain,(
% 1.36/0.55    r1_tarski(k2_relat_1(sK4),sK2) | ~spl5_1),
% 1.36/0.55    inference(subsumption_resolution,[],[f190,f111])).
% 1.36/0.55  fof(f190,plain,(
% 1.36/0.55    r1_tarski(k2_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(resolution,[],[f176,f74])).
% 1.36/0.55  fof(f176,plain,(
% 1.36/0.55    v5_relat_1(sK4,sK2)),
% 1.36/0.55    inference(resolution,[],[f58,f84])).
% 1.36/0.55  fof(f181,plain,(
% 1.36/0.55    spl5_1),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f180])).
% 1.36/0.55  fof(f180,plain,(
% 1.36/0.55    $false | spl5_1),
% 1.36/0.55    inference(subsumption_resolution,[],[f173,f112])).
% 1.36/0.55  fof(f112,plain,(
% 1.36/0.55    ~v1_relat_1(sK4) | spl5_1),
% 1.36/0.55    inference(avatar_component_clause,[],[f110])).
% 1.36/0.55  fof(f173,plain,(
% 1.36/0.55    v1_relat_1(sK4)),
% 1.36/0.55    inference(resolution,[],[f58,f81])).
% 1.36/0.55  fof(f152,plain,(
% 1.36/0.55    ~spl5_1 | spl5_8),
% 1.36/0.55    inference(avatar_split_clause,[],[f148,f150,f110])).
% 1.36/0.55  fof(f148,plain,(
% 1.36/0.55    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_relat_1(sK4)) )),
% 1.36/0.55    inference(subsumption_resolution,[],[f107,f56])).
% 1.36/0.55  fof(f107,plain,(
% 1.36/0.55    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.36/0.55    inference(resolution,[],[f60,f76])).
% 1.36/0.55  fof(f76,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f33])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(flattening,[],[f32])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.36/0.55  fof(f60,plain,(
% 1.36/0.55    v2_funct_1(sK4)),
% 1.36/0.55    inference(cnf_transformation,[],[f48])).
% 1.36/0.55  fof(f147,plain,(
% 1.36/0.55    ~spl5_1 | spl5_7),
% 1.36/0.55    inference(avatar_split_clause,[],[f142,f144,f110])).
% 1.36/0.55  fof(f142,plain,(
% 1.36/0.55    k5_relat_1(k2_funct_1(sK4),sK4) = k6_relat_1(k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f106,f56])).
% 1.36/0.55  fof(f106,plain,(
% 1.36/0.55    k5_relat_1(k2_funct_1(sK4),sK4) = k6_relat_1(k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(resolution,[],[f60,f73])).
% 1.36/0.55  fof(f73,plain,(
% 1.36/0.55    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.36/0.55  fof(f135,plain,(
% 1.36/0.55    ~spl5_1 | spl5_5),
% 1.36/0.55    inference(avatar_split_clause,[],[f130,f132,f110])).
% 1.36/0.55  fof(f130,plain,(
% 1.36/0.55    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f104,f56])).
% 1.36/0.55  fof(f104,plain,(
% 1.36/0.55    k1_relat_1(sK4) = k2_relat_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(resolution,[],[f60,f71])).
% 1.36/0.55  fof(f71,plain,(
% 1.36/0.55    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.36/0.55  fof(f123,plain,(
% 1.36/0.55    ~spl5_1 | spl5_3),
% 1.36/0.55    inference(avatar_split_clause,[],[f118,f120,f110])).
% 1.36/0.55  fof(f118,plain,(
% 1.36/0.55    v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f102,f56])).
% 1.36/0.55  fof(f102,plain,(
% 1.36/0.55    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(resolution,[],[f60,f68])).
% 1.36/0.55  fof(f68,plain,(
% 1.36/0.55    ( ! [X0] : (~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f26])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f25])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f6])).
% 1.36/0.55  fof(f6,axiom,(
% 1.36/0.55    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.36/0.55  fof(f117,plain,(
% 1.36/0.55    ~spl5_1 | spl5_2),
% 1.36/0.55    inference(avatar_split_clause,[],[f108,f114,f110])).
% 1.36/0.55  fof(f108,plain,(
% 1.36/0.55    v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(subsumption_resolution,[],[f101,f56])).
% 1.36/0.55  fof(f101,plain,(
% 1.36/0.55    v1_relat_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.36/0.55    inference(resolution,[],[f60,f67])).
% 1.36/0.55  fof(f67,plain,(
% 1.36/0.55    ( ! [X0] : (~v2_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f26])).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (15248)------------------------------
% 1.36/0.55  % (15248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (15248)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (15248)Memory used [KB]: 11001
% 1.36/0.55  % (15248)Time elapsed: 0.105 s
% 1.36/0.55  % (15248)------------------------------
% 1.36/0.55  % (15248)------------------------------
% 1.36/0.55  % (15264)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.36/0.55  % (15244)Success in time 0.186 s
%------------------------------------------------------------------------------
