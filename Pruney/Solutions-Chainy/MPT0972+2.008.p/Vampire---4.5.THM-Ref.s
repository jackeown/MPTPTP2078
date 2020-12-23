%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 379 expanded)
%              Number of leaves         :   22 ( 126 expanded)
%              Depth                    :   18
%              Number of atoms          :  475 (2200 expanded)
%              Number of equality atoms :  145 ( 515 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f287,f403,f418,f450,f460,f461,f475,f491,f496])).

fof(f496,plain,
    ( ~ spl11_9
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f494,f106])).

fof(f106,plain,(
    ! [X1] : ~ sP2(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f494,plain,
    ( sP2(k1_xboole_0,k1_xboole_0)
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(backward_demodulation,[],[f306,f449])).

fof(f449,plain,
    ( k1_xboole_0 = sK5
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl11_18
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f306,plain,
    ( sP2(sK5,k1_xboole_0)
    | ~ spl11_9 ),
    inference(backward_demodulation,[],[f280,f289])).

fof(f289,plain,
    ( k1_xboole_0 = sK6
    | ~ spl11_9 ),
    inference(resolution,[],[f280,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f280,plain,
    ( sP2(sK5,sK6)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl11_9
  <=> sP2(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f491,plain,
    ( ~ spl11_9
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl11_9
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f489,f212])).

fof(f212,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f107,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f489,plain,
    ( ~ r2_relset_1(sK5,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl11_9
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(forward_demodulation,[],[f488,f445])).

fof(f445,plain,
    ( k1_xboole_0 = sK7
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl11_17
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f488,plain,
    ( ~ r2_relset_1(sK5,k1_xboole_0,sK7,k1_xboole_0)
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(forward_demodulation,[],[f424,f459])).

fof(f459,plain,
    ( k1_xboole_0 = sK8
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl11_20
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f424,plain,
    ( ~ r2_relset_1(sK5,k1_xboole_0,sK7,sK8)
    | ~ spl11_9 ),
    inference(backward_demodulation,[],[f69,f289])).

fof(f69,plain,(
    ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8)
    & ! [X4] :
        ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
        | ~ r2_hidden(X4,sK5) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f19,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK5,sK6,sK7,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK7,X4)
              | ~ r2_hidden(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK5,sK6,sK7,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK7,X4)
            | ~ r2_hidden(X4,sK5) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X3,sK5,sK6)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK5,sK6,sK7,sK8)
      & ! [X4] :
          ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
          | ~ r2_hidden(X4,sK5) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f475,plain,
    ( spl11_19
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f474,f278,f453])).

fof(f453,plain,
    ( spl11_19
  <=> m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f474,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_9 ),
    inference(forward_demodulation,[],[f473,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f473,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)))
    | ~ spl11_9 ),
    inference(forward_demodulation,[],[f67,f289])).

fof(f67,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f45])).

fof(f461,plain,
    ( spl11_16
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f435,f278,f439])).

fof(f439,plain,
    ( spl11_16
  <=> m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f435,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_9 ),
    inference(forward_demodulation,[],[f422,f101])).

fof(f422,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)))
    | ~ spl11_9 ),
    inference(backward_demodulation,[],[f64,f289])).

fof(f64,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f45])).

fof(f460,plain,
    ( ~ spl11_19
    | spl11_20
    | spl11_18
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f451,f278,f447,f457,f453])).

fof(f451,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK8
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_9 ),
    inference(resolution,[],[f423,f227])).

fof(f227,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X1,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f105,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( sP4(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f98,f101])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X2,X1,X0)
        & sP3(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f31,f41,f40,f39])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f105,plain,(
    ! [X2,X0] :
      ( ~ sP4(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f423,plain,
    ( v1_funct_2(sK8,sK5,k1_xboole_0)
    | ~ spl11_9 ),
    inference(backward_demodulation,[],[f66,f289])).

fof(f66,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f450,plain,
    ( ~ spl11_16
    | spl11_17
    | spl11_18
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f437,f278,f447,f443,f439])).

fof(f437,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_9 ),
    inference(resolution,[],[f421,f227])).

fof(f421,plain,
    ( v1_funct_2(sK7,sK5,k1_xboole_0)
    | ~ spl11_9 ),
    inference(backward_demodulation,[],[f63,f289])).

fof(f63,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f418,plain,
    ( spl11_8
    | spl11_9 ),
    inference(avatar_split_clause,[],[f417,f278,f274])).

fof(f274,plain,
    ( spl11_8
  <=> sK5 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f417,plain,
    ( sP2(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f322,f63])).

fof(f322,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP2(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(resolution,[],[f64,f245])).

fof(f245,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP2(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f243,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f243,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP2(X3,X4)
      | ~ sP3(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f93,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f403,plain,
    ( ~ spl11_8
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f390,f210])).

fof(f210,plain,(
    r2_relset_1(sK5,sK6,sK7,sK7) ),
    inference(resolution,[],[f107,f64])).

fof(f390,plain,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK7)
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(backward_demodulation,[],[f69,f386])).

fof(f386,plain,
    ( sK7 = sK8
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f385,f108])).

fof(f108,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f87,f64])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f385,plain,
    ( sK7 = sK8
    | ~ v1_relat_1(sK7)
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f384,f62])).

fof(f62,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f384,plain,
    ( sK7 = sK8
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f383,f276])).

fof(f276,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f274])).

fof(f383,plain,
    ( sK5 != k1_relat_1(sK7)
    | sK7 = sK8
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl11_10 ),
    inference(equality_resolution,[],[f377])).

fof(f377,plain,
    ( ! [X0] :
        ( k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0))
        | k1_relat_1(X0) != sK5
        | sK8 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f376,f343])).

fof(f343,plain,
    ( ! [X1] :
        ( r2_hidden(sK9(sK8,X1),sK5)
        | sK8 = X1
        | k1_relat_1(X1) != sK5
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f342,f109])).

fof(f109,plain,(
    v1_relat_1(sK8) ),
    inference(resolution,[],[f87,f67])).

fof(f342,plain,
    ( ! [X1] :
        ( r2_hidden(sK9(sK8,X1),sK5)
        | sK8 = X1
        | k1_relat_1(X1) != sK5
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK8) )
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f338,f65])).

fof(f65,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f338,plain,
    ( ! [X1] :
        ( r2_hidden(sK9(sK8,X1),sK5)
        | sK8 = X1
        | k1_relat_1(X1) != sK5
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK8)
        | ~ v1_relat_1(sK8) )
    | ~ spl11_10 ),
    inference(superposition,[],[f72,f286])).

fof(f286,plain,
    ( sK5 = k1_relat_1(sK8)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl11_10
  <=> sK5 = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK9(X0,X1)) != k1_funct_1(X1,sK9(X0,X1))
            & r2_hidden(sK9(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1)) != k1_funct_1(X1,sK9(X0,X1))
        & r2_hidden(sK9(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f376,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK5
        | k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0))
        | sK8 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK9(sK8,X0),sK5) )
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f375,f286])).

fof(f375,plain,(
    ! [X0] :
      ( k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0))
      | sK8 = X0
      | k1_relat_1(X0) != k1_relat_1(sK8)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK9(sK8,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f374,f109])).

fof(f374,plain,(
    ! [X0] :
      ( k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0))
      | sK8 = X0
      | k1_relat_1(X0) != k1_relat_1(sK8)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK8)
      | ~ r2_hidden(sK9(sK8,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f370,f65])).

fof(f370,plain,(
    ! [X0] :
      ( k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0))
      | sK8 = X0
      | k1_relat_1(X0) != k1_relat_1(sK8)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK8)
      | ~ v1_relat_1(sK8)
      | ~ r2_hidden(sK9(sK8,X0),sK5) ) ),
    inference(superposition,[],[f73,f68])).

fof(f68,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
      | ~ r2_hidden(X4,sK5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK9(X0,X1)) != k1_funct_1(X1,sK9(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f287,plain,
    ( spl11_10
    | spl11_9 ),
    inference(avatar_split_clause,[],[f282,f278,f284])).

fof(f282,plain,
    ( sP2(sK5,sK6)
    | sK5 = k1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f267,f66])).

fof(f267,plain,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | sP2(sK5,sK6)
    | sK5 = k1_relat_1(sK8) ),
    inference(resolution,[],[f245,f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:09:01 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.47  % (19542)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.48  % (19542)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f497,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f287,f403,f418,f450,f460,f461,f475,f491,f496])).
% 0.22/0.48  fof(f496,plain,(
% 0.22/0.48    ~spl11_9 | ~spl11_18),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f495])).
% 0.22/0.48  fof(f495,plain,(
% 0.22/0.48    $false | (~spl11_9 | ~spl11_18)),
% 0.22/0.48    inference(subsumption_resolution,[],[f494,f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ( ! [X1] : (~sP2(k1_xboole_0,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP2(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.48  fof(f494,plain,(
% 0.22/0.48    sP2(k1_xboole_0,k1_xboole_0) | (~spl11_9 | ~spl11_18)),
% 0.22/0.48    inference(backward_demodulation,[],[f306,f449])).
% 0.22/0.48  fof(f449,plain,(
% 0.22/0.48    k1_xboole_0 = sK5 | ~spl11_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f447])).
% 0.22/0.48  fof(f447,plain,(
% 0.22/0.48    spl11_18 <=> k1_xboole_0 = sK5),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.22/0.48  fof(f306,plain,(
% 0.22/0.48    sP2(sK5,k1_xboole_0) | ~spl11_9),
% 0.22/0.48    inference(backward_demodulation,[],[f280,f289])).
% 0.22/0.48  fof(f289,plain,(
% 0.22/0.48    k1_xboole_0 = sK6 | ~spl11_9),
% 0.22/0.48    inference(resolution,[],[f280,f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~sP2(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f61])).
% 0.22/0.48  fof(f280,plain,(
% 0.22/0.48    sP2(sK5,sK6) | ~spl11_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f278])).
% 0.22/0.48  fof(f278,plain,(
% 0.22/0.48    spl11_9 <=> sP2(sK5,sK6)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.22/0.48  fof(f491,plain,(
% 0.22/0.48    ~spl11_9 | ~spl11_17 | ~spl11_20),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f490])).
% 0.22/0.48  fof(f490,plain,(
% 0.22/0.48    $false | (~spl11_9 | ~spl11_17 | ~spl11_20)),
% 0.22/0.48    inference(subsumption_resolution,[],[f489,f212])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.22/0.48    inference(resolution,[],[f107,f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.48    inference(condensation,[],[f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.48  fof(f489,plain,(
% 0.22/0.48    ~r2_relset_1(sK5,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl11_9 | ~spl11_17 | ~spl11_20)),
% 0.22/0.48    inference(forward_demodulation,[],[f488,f445])).
% 0.22/0.48  fof(f445,plain,(
% 0.22/0.48    k1_xboole_0 = sK7 | ~spl11_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f443])).
% 0.22/0.48  fof(f443,plain,(
% 0.22/0.48    spl11_17 <=> k1_xboole_0 = sK7),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 0.22/0.48  fof(f488,plain,(
% 0.22/0.48    ~r2_relset_1(sK5,k1_xboole_0,sK7,k1_xboole_0) | (~spl11_9 | ~spl11_20)),
% 0.22/0.48    inference(forward_demodulation,[],[f424,f459])).
% 0.22/0.48  fof(f459,plain,(
% 0.22/0.48    k1_xboole_0 = sK8 | ~spl11_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f457])).
% 0.22/0.48  fof(f457,plain,(
% 0.22/0.48    spl11_20 <=> k1_xboole_0 = sK8),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 0.22/0.48  fof(f424,plain,(
% 0.22/0.48    ~r2_relset_1(sK5,k1_xboole_0,sK7,sK8) | ~spl11_9),
% 0.22/0.48    inference(backward_demodulation,[],[f69,f289])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~r2_relset_1(sK5,sK6,sK7,sK8)),
% 0.22/0.48    inference(cnf_transformation,[],[f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    (~r2_relset_1(sK5,sK6,sK7,sK8) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f19,f44,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK5,sK6,sK7,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK7,X4) | ~r2_hidden(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ? [X3] : (~r2_relset_1(sK5,sK6,sK7,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK7,X4) | ~r2_hidden(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) => (~r2_relset_1(sK5,sK6,sK7,sK8) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.48    inference(negated_conjecture,[],[f16])).
% 0.22/0.48  fof(f16,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.22/0.48  fof(f475,plain,(
% 0.22/0.48    spl11_19 | ~spl11_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f474,f278,f453])).
% 0.22/0.48  fof(f453,plain,(
% 0.22/0.48    spl11_19 <=> m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 0.22/0.48  fof(f474,plain,(
% 0.22/0.48    m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) | ~spl11_9),
% 0.22/0.48    inference(forward_demodulation,[],[f473,f101])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.48    inference(flattening,[],[f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.48  fof(f473,plain,(
% 0.22/0.48    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) | ~spl11_9),
% 0.22/0.48    inference(forward_demodulation,[],[f67,f289])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.22/0.48    inference(cnf_transformation,[],[f45])).
% 0.22/0.48  fof(f461,plain,(
% 0.22/0.48    spl11_16 | ~spl11_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f435,f278,f439])).
% 0.22/0.48  fof(f439,plain,(
% 0.22/0.48    spl11_16 <=> m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.22/0.48  fof(f435,plain,(
% 0.22/0.48    m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) | ~spl11_9),
% 0.22/0.48    inference(forward_demodulation,[],[f422,f101])).
% 0.22/0.48  fof(f422,plain,(
% 0.22/0.48    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) | ~spl11_9),
% 0.22/0.48    inference(backward_demodulation,[],[f64,f289])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.22/0.48    inference(cnf_transformation,[],[f45])).
% 0.22/0.48  fof(f460,plain,(
% 0.22/0.48    ~spl11_19 | spl11_20 | spl11_18 | ~spl11_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f451,f278,f447,f457,f453])).
% 0.22/0.48  fof(f451,plain,(
% 0.22/0.48    k1_xboole_0 = sK5 | k1_xboole_0 = sK8 | ~m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) | ~spl11_9),
% 0.22/0.48    inference(resolution,[],[f423,f227])).
% 0.22/0.48  fof(f227,plain,(
% 0.22/0.48    ( ! [X2,X1] : (~v1_funct_2(X1,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f105,f197])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP4(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.48    inference(superposition,[],[f98,f101])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X2,X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(definition_folding,[],[f31,f41,f40,f39])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ( ! [X2,X0] : (~sP4(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(equality_resolution,[],[f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP4(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP4(X0,X1,X2))),
% 0.22/0.48    inference(rectify,[],[f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f41])).
% 0.22/0.48  fof(f423,plain,(
% 0.22/0.48    v1_funct_2(sK8,sK5,k1_xboole_0) | ~spl11_9),
% 0.22/0.48    inference(backward_demodulation,[],[f66,f289])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    v1_funct_2(sK8,sK5,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f45])).
% 0.22/0.48  fof(f450,plain,(
% 0.22/0.48    ~spl11_16 | spl11_17 | spl11_18 | ~spl11_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f437,f278,f447,f443,f439])).
% 0.22/0.48  fof(f437,plain,(
% 0.22/0.48    k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) | ~spl11_9),
% 0.22/0.48    inference(resolution,[],[f421,f227])).
% 0.22/0.48  fof(f421,plain,(
% 0.22/0.48    v1_funct_2(sK7,sK5,k1_xboole_0) | ~spl11_9),
% 0.22/0.48    inference(backward_demodulation,[],[f63,f289])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v1_funct_2(sK7,sK5,sK6)),
% 0.22/0.49    inference(cnf_transformation,[],[f45])).
% 0.22/0.49  fof(f418,plain,(
% 0.22/0.49    spl11_8 | spl11_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f417,f278,f274])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    spl11_8 <=> sK5 = k1_relat_1(sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.22/0.49  fof(f417,plain,(
% 0.22/0.49    sP2(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f322,f63])).
% 0.22/0.49  fof(f322,plain,(
% 0.22/0.49    ~v1_funct_2(sK7,sK5,sK6) | sP2(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 0.22/0.49    inference(resolution,[],[f64,f245])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP2(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f243,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP2(X3,X4) | ~sP3(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.49    inference(superposition,[],[f93,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP2(X0,X2) | ~sP3(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP2(X0,X2) | ~sP3(X0,X1,X2))),
% 0.22/0.49    inference(rectify,[],[f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f40])).
% 0.22/0.49  fof(f403,plain,(
% 0.22/0.49    ~spl11_8 | ~spl11_10),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f402])).
% 0.22/0.49  fof(f402,plain,(
% 0.22/0.49    $false | (~spl11_8 | ~spl11_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f390,f210])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    r2_relset_1(sK5,sK6,sK7,sK7)),
% 0.22/0.49    inference(resolution,[],[f107,f64])).
% 0.22/0.49  fof(f390,plain,(
% 0.22/0.49    ~r2_relset_1(sK5,sK6,sK7,sK7) | (~spl11_8 | ~spl11_10)),
% 0.22/0.49    inference(backward_demodulation,[],[f69,f386])).
% 0.22/0.49  fof(f386,plain,(
% 0.22/0.49    sK7 = sK8 | (~spl11_8 | ~spl11_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f385,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    v1_relat_1(sK7)),
% 0.22/0.49    inference(resolution,[],[f87,f64])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f385,plain,(
% 0.22/0.49    sK7 = sK8 | ~v1_relat_1(sK7) | (~spl11_8 | ~spl11_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f384,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    v1_funct_1(sK7)),
% 0.22/0.49    inference(cnf_transformation,[],[f45])).
% 0.22/0.49  fof(f384,plain,(
% 0.22/0.49    sK7 = sK8 | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | (~spl11_8 | ~spl11_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f383,f276])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    sK5 = k1_relat_1(sK7) | ~spl11_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f274])).
% 0.22/0.49  fof(f383,plain,(
% 0.22/0.49    sK5 != k1_relat_1(sK7) | sK7 = sK8 | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl11_10),
% 0.22/0.49    inference(equality_resolution,[],[f377])).
% 0.22/0.49  fof(f377,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0)) | k1_relat_1(X0) != sK5 | sK8 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl11_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f376,f343])).
% 0.22/0.49  fof(f343,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(sK9(sK8,X1),sK5) | sK8 = X1 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl11_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f342,f109])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    v1_relat_1(sK8)),
% 0.22/0.49    inference(resolution,[],[f87,f67])).
% 0.22/0.49  fof(f342,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(sK9(sK8,X1),sK5) | sK8 = X1 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK8)) ) | ~spl11_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f338,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    v1_funct_1(sK8)),
% 0.22/0.49    inference(cnf_transformation,[],[f45])).
% 0.22/0.49  fof(f338,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(sK9(sK8,X1),sK5) | sK8 = X1 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8)) ) | ~spl11_10),
% 0.22/0.49    inference(superposition,[],[f72,f286])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    sK5 = k1_relat_1(sK8) | ~spl11_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f284])).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    spl11_10 <=> sK5 = k1_relat_1(sK8)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK9(X0,X1)) != k1_funct_1(X1,sK9(X0,X1)) & r2_hidden(sK9(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK9(X0,X1)) != k1_funct_1(X1,sK9(X0,X1)) & r2_hidden(sK9(X0,X1),k1_relat_1(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.49  fof(f376,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(X0) != sK5 | k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0)) | sK8 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK9(sK8,X0),sK5)) ) | ~spl11_10),
% 0.22/0.49    inference(forward_demodulation,[],[f375,f286])).
% 0.22/0.49  fof(f375,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0)) | sK8 = X0 | k1_relat_1(X0) != k1_relat_1(sK8) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK9(sK8,X0),sK5)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f374,f109])).
% 0.22/0.49  fof(f374,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0)) | sK8 = X0 | k1_relat_1(X0) != k1_relat_1(sK8) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK8) | ~r2_hidden(sK9(sK8,X0),sK5)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f370,f65])).
% 0.22/0.49  fof(f370,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(sK7,sK9(sK8,X0)) != k1_funct_1(X0,sK9(sK8,X0)) | sK8 = X0 | k1_relat_1(X0) != k1_relat_1(sK8) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~r2_hidden(sK9(sK8,X0),sK5)) )),
% 0.22/0.49    inference(superposition,[],[f73,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f45])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_funct_1(X0,sK9(X0,X1)) != k1_funct_1(X1,sK9(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f47])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    spl11_10 | spl11_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f282,f278,f284])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    sP2(sK5,sK6) | sK5 = k1_relat_1(sK8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f267,f66])).
% 0.22/0.49  fof(f267,plain,(
% 0.22/0.49    ~v1_funct_2(sK8,sK5,sK6) | sP2(sK5,sK6) | sK5 = k1_relat_1(sK8)),
% 0.22/0.49    inference(resolution,[],[f245,f67])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (19542)------------------------------
% 0.22/0.49  % (19542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19542)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (19542)Memory used [KB]: 6396
% 0.22/0.49  % (19542)Time elapsed: 0.041 s
% 0.22/0.49  % (19542)------------------------------
% 0.22/0.49  % (19542)------------------------------
% 0.22/0.49  % (19537)Success in time 0.126 s
%------------------------------------------------------------------------------
