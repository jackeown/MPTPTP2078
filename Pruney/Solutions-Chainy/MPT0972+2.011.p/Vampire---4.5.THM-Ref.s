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
% DateTime   : Thu Dec  3 13:01:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 380 expanded)
%              Number of leaves         :   24 ( 130 expanded)
%              Depth                    :   14
%              Number of atoms          :  517 (2245 expanded)
%              Number of equality atoms :  142 ( 465 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f603,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f298,f311,f377,f444,f472,f490,f500,f541,f552,f602])).

fof(f602,plain,
    ( spl10_7
    | ~ spl10_13
    | spl10_16
    | ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | spl10_7
    | ~ spl10_13
    | spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f566,f556])).

fof(f556,plain,
    ( k1_xboole_0 != sK6
    | spl10_7
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f296,f540])).

fof(f540,plain,
    ( k1_xboole_0 = sK5
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f538])).

fof(f538,plain,
    ( spl10_18
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f296,plain,
    ( sK5 != sK6
    | spl10_7 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl10_7
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f566,plain,
    ( k1_xboole_0 = sK6
    | ~ spl10_13
    | spl10_16 ),
    inference(subsumption_resolution,[],[f565,f451])).

fof(f451,plain,
    ( k1_xboole_0 != sK3
    | spl10_16 ),
    inference(avatar_component_clause,[],[f450])).

fof(f450,plain,
    ( spl10_16
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f565,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK6
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f564,f512])).

fof(f512,plain,
    ( v1_funct_2(sK6,sK3,k1_xboole_0)
    | ~ spl10_13 ),
    inference(backward_demodulation,[],[f57,f379])).

fof(f379,plain,
    ( k1_xboole_0 = sK4
    | ~ spl10_13 ),
    inference(resolution,[],[f370,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f370,plain,
    ( sP0(sK3,sK4)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl10_13
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f57,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f33,f32])).

fof(f32,plain,
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
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
              | ~ r2_hidden(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK3,sK4,sK5,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
            | ~ r2_hidden(X4,sK3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
      & ! [X4] :
          ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
          | ~ r2_hidden(X4,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f564,plain,
    ( ~ v1_funct_2(sK6,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK6
    | ~ spl10_13 ),
    inference(resolution,[],[f520,f95])).

fof(f95,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f520,plain,
    ( sP2(sK6,k1_xboole_0,sK3)
    | ~ spl10_13 ),
    inference(backward_demodulation,[],[f140,f379])).

fof(f140,plain,(
    sP2(sK6,sK4,sK3) ),
    inference(resolution,[],[f87,f58])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f25,f30,f29,f28])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f552,plain,
    ( ~ spl10_13
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f544,f96])).

fof(f96,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f544,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl10_13
    | ~ spl10_16 ),
    inference(backward_demodulation,[],[f393,f452])).

fof(f452,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f450])).

fof(f393,plain,
    ( sP0(sK3,k1_xboole_0)
    | ~ spl10_13 ),
    inference(backward_demodulation,[],[f370,f379])).

fof(f541,plain,
    ( spl10_18
    | spl10_16
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f536,f368,f450,f538])).

fof(f536,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f535,f510])).

fof(f510,plain,
    ( v1_funct_2(sK5,sK3,k1_xboole_0)
    | ~ spl10_13 ),
    inference(backward_demodulation,[],[f54,f379])).

fof(f54,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f535,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ spl10_13 ),
    inference(resolution,[],[f519,f95])).

fof(f519,plain,
    ( sP2(sK5,k1_xboole_0,sK3)
    | ~ spl10_13 ),
    inference(backward_demodulation,[],[f139,f379])).

fof(f139,plain,(
    sP2(sK5,sK4,sK3) ),
    inference(resolution,[],[f87,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f500,plain,
    ( spl10_12
    | spl10_13 ),
    inference(avatar_split_clause,[],[f430,f368,f364])).

fof(f364,plain,
    ( spl10_12
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f430,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f429,f54])).

fof(f429,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(resolution,[],[f55,f217])).

fof(f217,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f215,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f215,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f82,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f490,plain,(
    ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f478,f168])).

fof(f168,plain,(
    r2_relset_1(sK3,sK4,sK5,sK5) ),
    inference(resolution,[],[f97,f55])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f478,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK5)
    | ~ spl10_7 ),
    inference(backward_demodulation,[],[f60,f297])).

fof(f297,plain,
    ( sK5 = sK6
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f295])).

fof(f60,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f472,plain,
    ( spl10_8
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | spl10_8
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f470,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f470,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl10_8
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f310,f366])).

fof(f366,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f364])).

fof(f310,plain,
    ( ~ r1_tarski(k1_relat_1(sK5),sK3)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl10_8
  <=> r1_tarski(k1_relat_1(sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f444,plain,
    ( ~ spl10_14
    | spl10_6
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f433,f364,f291,f374])).

fof(f374,plain,
    ( spl10_14
  <=> sK3 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f291,plain,
    ( spl10_6
  <=> k1_relat_1(sK6) = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f433,plain,
    ( sK3 != k1_relat_1(sK6)
    | spl10_6
    | ~ spl10_12 ),
    inference(backward_demodulation,[],[f293,f366])).

fof(f293,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f291])).

fof(f377,plain,
    ( spl10_14
    | spl10_13 ),
    inference(avatar_split_clause,[],[f372,f368,f374])).

fof(f372,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f358,f57])).

fof(f358,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(resolution,[],[f217,f58])).

fof(f311,plain,
    ( ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_5 ),
    inference(avatar_split_clause,[],[f306,f287,f308,f295,f291])).

fof(f287,plain,
    ( spl10_5
  <=> r2_hidden(sK7(sK6,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f306,plain,
    ( ~ r1_tarski(k1_relat_1(sK5),sK3)
    | sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | spl10_5 ),
    inference(inner_rewriting,[],[f305])).

fof(f305,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),sK3)
    | sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | spl10_5 ),
    inference(subsumption_resolution,[],[f304,f101])).

fof(f101,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f76,f58])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f304,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),sK3)
    | sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | spl10_5 ),
    inference(subsumption_resolution,[],[f303,f56])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f303,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),sK3)
    | sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl10_5 ),
    inference(subsumption_resolution,[],[f302,f100])).

fof(f100,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f76,f55])).

fof(f302,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),sK3)
    | sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl10_5 ),
    inference(subsumption_resolution,[],[f300,f53])).

fof(f53,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f300,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),sK3)
    | sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl10_5 ),
    inference(resolution,[],[f299,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
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
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f299,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK6,sK5),X0)
        | ~ r1_tarski(X0,sK3) )
    | spl10_5 ),
    inference(resolution,[],[f289,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f289,plain,
    ( ~ r2_hidden(sK7(sK6,sK5),sK3)
    | spl10_5 ),
    inference(avatar_component_clause,[],[f287])).

fof(f298,plain,
    ( ~ spl10_5
    | ~ spl10_6
    | spl10_7 ),
    inference(avatar_split_clause,[],[f285,f295,f291,f287])).

fof(f285,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ r2_hidden(sK7(sK6,sK5),sK3) ),
    inference(subsumption_resolution,[],[f284,f100])).

fof(f284,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ r2_hidden(sK7(sK6,sK5),sK3) ),
    inference(subsumption_resolution,[],[f283,f53])).

fof(f283,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ r2_hidden(sK7(sK6,sK5),sK3) ),
    inference(equality_resolution,[],[f279])).

fof(f279,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK7(sK6,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f278,f101])).

fof(f278,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK6)
      | ~ r2_hidden(sK7(sK6,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f274,f56])).

fof(f274,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ r2_hidden(sK7(sK6,X0),sK3) ) ),
    inference(superposition,[],[f63,f59])).

fof(f59,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (8060)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (8052)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (8060)Refutation not found, incomplete strategy% (8060)------------------------------
% 0.22/0.51  % (8060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8060)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8060)Memory used [KB]: 10746
% 0.22/0.52  % (8060)Time elapsed: 0.103 s
% 0.22/0.52  % (8060)------------------------------
% 0.22/0.52  % (8060)------------------------------
% 0.22/0.52  % (8056)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (8058)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (8074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (8054)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (8061)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (8057)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (8053)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (8076)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (8064)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (8063)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (8062)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (8066)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (8055)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (8077)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (8079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (8081)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (8078)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (8071)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (8073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (8070)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (8069)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (8074)Refutation not found, incomplete strategy% (8074)------------------------------
% 0.22/0.56  % (8074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8069)Refutation not found, incomplete strategy% (8069)------------------------------
% 0.22/0.56  % (8069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8069)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8069)Memory used [KB]: 10746
% 0.22/0.56  % (8069)Time elapsed: 0.149 s
% 0.22/0.56  % (8069)------------------------------
% 0.22/0.56  % (8069)------------------------------
% 0.22/0.56  % (8074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8074)Memory used [KB]: 11001
% 0.22/0.56  % (8074)Time elapsed: 0.138 s
% 0.22/0.56  % (8074)------------------------------
% 0.22/0.56  % (8074)------------------------------
% 0.22/0.56  % (8065)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (8062)Refutation not found, incomplete strategy% (8062)------------------------------
% 0.22/0.56  % (8062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8062)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8062)Memory used [KB]: 10746
% 0.22/0.56  % (8062)Time elapsed: 0.153 s
% 0.22/0.56  % (8062)------------------------------
% 0.22/0.56  % (8062)------------------------------
% 0.22/0.56  % (8072)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (8068)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (8080)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (8075)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (8067)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.58  % (8079)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f603,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f298,f311,f377,f444,f472,f490,f500,f541,f552,f602])).
% 0.22/0.58  fof(f602,plain,(
% 0.22/0.58    spl10_7 | ~spl10_13 | spl10_16 | ~spl10_18),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f601])).
% 0.22/0.58  fof(f601,plain,(
% 0.22/0.58    $false | (spl10_7 | ~spl10_13 | spl10_16 | ~spl10_18)),
% 0.22/0.58    inference(subsumption_resolution,[],[f566,f556])).
% 0.22/0.58  fof(f556,plain,(
% 0.22/0.58    k1_xboole_0 != sK6 | (spl10_7 | ~spl10_18)),
% 0.22/0.58    inference(backward_demodulation,[],[f296,f540])).
% 0.22/0.58  fof(f540,plain,(
% 0.22/0.58    k1_xboole_0 = sK5 | ~spl10_18),
% 0.22/0.58    inference(avatar_component_clause,[],[f538])).
% 0.22/0.58  fof(f538,plain,(
% 0.22/0.58    spl10_18 <=> k1_xboole_0 = sK5),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.22/0.58  fof(f296,plain,(
% 0.22/0.58    sK5 != sK6 | spl10_7),
% 0.22/0.58    inference(avatar_component_clause,[],[f295])).
% 0.22/0.58  fof(f295,plain,(
% 0.22/0.58    spl10_7 <=> sK5 = sK6),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.58  fof(f566,plain,(
% 0.22/0.58    k1_xboole_0 = sK6 | (~spl10_13 | spl10_16)),
% 0.22/0.58    inference(subsumption_resolution,[],[f565,f451])).
% 0.22/0.58  fof(f451,plain,(
% 0.22/0.58    k1_xboole_0 != sK3 | spl10_16),
% 0.22/0.58    inference(avatar_component_clause,[],[f450])).
% 0.22/0.58  fof(f450,plain,(
% 0.22/0.58    spl10_16 <=> k1_xboole_0 = sK3),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.22/0.58  fof(f565,plain,(
% 0.22/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK6 | ~spl10_13),
% 0.22/0.58    inference(subsumption_resolution,[],[f564,f512])).
% 0.22/0.58  fof(f512,plain,(
% 0.22/0.58    v1_funct_2(sK6,sK3,k1_xboole_0) | ~spl10_13),
% 0.22/0.58    inference(backward_demodulation,[],[f57,f379])).
% 0.22/0.58  fof(f379,plain,(
% 0.22/0.58    k1_xboole_0 = sK4 | ~spl10_13),
% 0.22/0.58    inference(resolution,[],[f370,f84])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.58  fof(f370,plain,(
% 0.22/0.58    sP0(sK3,sK4) | ~spl10_13),
% 0.22/0.58    inference(avatar_component_clause,[],[f368])).
% 0.22/0.58  fof(f368,plain,(
% 0.22/0.58    spl10_13 <=> sP0(sK3,sK4)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    v1_funct_2(sK6,sK3,sK4)),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f33,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.58    inference(flattening,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.58    inference(ennf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.58    inference(negated_conjecture,[],[f13])).
% 0.22/0.58  fof(f13,conjecture,(
% 0.22/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.22/0.58  fof(f564,plain,(
% 0.22/0.58    ~v1_funct_2(sK6,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK6 | ~spl10_13),
% 0.22/0.58    inference(resolution,[],[f520,f95])).
% 0.22/0.58  fof(f95,plain,(
% 0.22/0.58    ( ! [X2,X0] : (~sP2(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(equality_resolution,[],[f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.22/0.58    inference(rectify,[],[f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.22/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.58  fof(f520,plain,(
% 0.22/0.58    sP2(sK6,k1_xboole_0,sK3) | ~spl10_13),
% 0.22/0.58    inference(backward_demodulation,[],[f140,f379])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    sP2(sK6,sK4,sK3)),
% 0.22/0.58    inference(resolution,[],[f87,f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(definition_folding,[],[f25,f30,f29,f28])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(flattening,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.59  fof(f552,plain,(
% 0.22/0.59    ~spl10_13 | ~spl10_16),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f551])).
% 0.22/0.59  fof(f551,plain,(
% 0.22/0.59    $false | (~spl10_13 | ~spl10_16)),
% 0.22/0.59    inference(subsumption_resolution,[],[f544,f96])).
% 0.22/0.59  fof(f96,plain,(
% 0.22/0.59    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f85])).
% 0.22/0.59  fof(f85,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f544,plain,(
% 0.22/0.59    sP0(k1_xboole_0,k1_xboole_0) | (~spl10_13 | ~spl10_16)),
% 0.22/0.59    inference(backward_demodulation,[],[f393,f452])).
% 0.22/0.59  fof(f452,plain,(
% 0.22/0.59    k1_xboole_0 = sK3 | ~spl10_16),
% 0.22/0.59    inference(avatar_component_clause,[],[f450])).
% 0.22/0.59  fof(f393,plain,(
% 0.22/0.59    sP0(sK3,k1_xboole_0) | ~spl10_13),
% 0.22/0.59    inference(backward_demodulation,[],[f370,f379])).
% 0.22/0.59  fof(f541,plain,(
% 0.22/0.59    spl10_18 | spl10_16 | ~spl10_13),
% 0.22/0.59    inference(avatar_split_clause,[],[f536,f368,f450,f538])).
% 0.22/0.59  fof(f536,plain,(
% 0.22/0.59    k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~spl10_13),
% 0.22/0.59    inference(subsumption_resolution,[],[f535,f510])).
% 0.22/0.59  fof(f510,plain,(
% 0.22/0.59    v1_funct_2(sK5,sK3,k1_xboole_0) | ~spl10_13),
% 0.22/0.59    inference(backward_demodulation,[],[f54,f379])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    v1_funct_2(sK5,sK3,sK4)),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f535,plain,(
% 0.22/0.59    ~v1_funct_2(sK5,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~spl10_13),
% 0.22/0.59    inference(resolution,[],[f519,f95])).
% 0.22/0.59  fof(f519,plain,(
% 0.22/0.59    sP2(sK5,k1_xboole_0,sK3) | ~spl10_13),
% 0.22/0.59    inference(backward_demodulation,[],[f139,f379])).
% 0.22/0.59  fof(f139,plain,(
% 0.22/0.59    sP2(sK5,sK4,sK3)),
% 0.22/0.59    inference(resolution,[],[f87,f55])).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f500,plain,(
% 0.22/0.59    spl10_12 | spl10_13),
% 0.22/0.59    inference(avatar_split_clause,[],[f430,f368,f364])).
% 0.22/0.59  fof(f364,plain,(
% 0.22/0.59    spl10_12 <=> sK3 = k1_relat_1(sK5)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.22/0.59  fof(f430,plain,(
% 0.22/0.59    sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.22/0.59    inference(subsumption_resolution,[],[f429,f54])).
% 0.22/0.59  fof(f429,plain,(
% 0.22/0.59    ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.22/0.59    inference(resolution,[],[f55,f217])).
% 0.22/0.59  fof(f217,plain,(
% 0.22/0.59    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f215,f86])).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f31])).
% 0.22/0.59  fof(f215,plain,(
% 0.22/0.59    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.59    inference(superposition,[],[f82,f77])).
% 0.22/0.59  fof(f77,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.59  fof(f82,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.22/0.59    inference(rectify,[],[f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.59    inference(nnf_transformation,[],[f29])).
% 0.22/0.59  fof(f490,plain,(
% 0.22/0.59    ~spl10_7),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f489])).
% 0.22/0.59  fof(f489,plain,(
% 0.22/0.59    $false | ~spl10_7),
% 0.22/0.59    inference(subsumption_resolution,[],[f478,f168])).
% 0.22/0.59  fof(f168,plain,(
% 0.22/0.59    r2_relset_1(sK3,sK4,sK5,sK5)),
% 0.22/0.59    inference(resolution,[],[f97,f55])).
% 0.22/0.59  fof(f97,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.59    inference(condensation,[],[f88])).
% 0.22/0.59  fof(f88,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(flattening,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.59  fof(f478,plain,(
% 0.22/0.59    ~r2_relset_1(sK3,sK4,sK5,sK5) | ~spl10_7),
% 0.22/0.59    inference(backward_demodulation,[],[f60,f297])).
% 0.22/0.59  fof(f297,plain,(
% 0.22/0.59    sK5 = sK6 | ~spl10_7),
% 0.22/0.59    inference(avatar_component_clause,[],[f295])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f472,plain,(
% 0.22/0.59    spl10_8 | ~spl10_12),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f471])).
% 0.22/0.59  fof(f471,plain,(
% 0.22/0.59    $false | (spl10_8 | ~spl10_12)),
% 0.22/0.59    inference(subsumption_resolution,[],[f470,f89])).
% 0.22/0.59  fof(f89,plain,(
% 0.22/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f68])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(flattening,[],[f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(nnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.59  fof(f470,plain,(
% 0.22/0.59    ~r1_tarski(sK3,sK3) | (spl10_8 | ~spl10_12)),
% 0.22/0.59    inference(forward_demodulation,[],[f310,f366])).
% 0.22/0.59  fof(f366,plain,(
% 0.22/0.59    sK3 = k1_relat_1(sK5) | ~spl10_12),
% 0.22/0.59    inference(avatar_component_clause,[],[f364])).
% 0.22/0.59  fof(f310,plain,(
% 0.22/0.59    ~r1_tarski(k1_relat_1(sK5),sK3) | spl10_8),
% 0.22/0.59    inference(avatar_component_clause,[],[f308])).
% 0.22/0.59  fof(f308,plain,(
% 0.22/0.59    spl10_8 <=> r1_tarski(k1_relat_1(sK5),sK3)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.59  fof(f444,plain,(
% 0.22/0.59    ~spl10_14 | spl10_6 | ~spl10_12),
% 0.22/0.59    inference(avatar_split_clause,[],[f433,f364,f291,f374])).
% 0.22/0.59  fof(f374,plain,(
% 0.22/0.59    spl10_14 <=> sK3 = k1_relat_1(sK6)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.22/0.59  fof(f291,plain,(
% 0.22/0.59    spl10_6 <=> k1_relat_1(sK6) = k1_relat_1(sK5)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.59  fof(f433,plain,(
% 0.22/0.59    sK3 != k1_relat_1(sK6) | (spl10_6 | ~spl10_12)),
% 0.22/0.59    inference(backward_demodulation,[],[f293,f366])).
% 0.22/0.59  fof(f293,plain,(
% 0.22/0.59    k1_relat_1(sK6) != k1_relat_1(sK5) | spl10_6),
% 0.22/0.59    inference(avatar_component_clause,[],[f291])).
% 0.22/0.59  fof(f377,plain,(
% 0.22/0.59    spl10_14 | spl10_13),
% 0.22/0.59    inference(avatar_split_clause,[],[f372,f368,f374])).
% 0.22/0.59  fof(f372,plain,(
% 0.22/0.59    sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 0.22/0.59    inference(subsumption_resolution,[],[f358,f57])).
% 0.22/0.59  fof(f358,plain,(
% 0.22/0.59    ~v1_funct_2(sK6,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 0.22/0.59    inference(resolution,[],[f217,f58])).
% 0.22/0.59  fof(f311,plain,(
% 0.22/0.59    ~spl10_6 | spl10_7 | ~spl10_8 | spl10_5),
% 0.22/0.59    inference(avatar_split_clause,[],[f306,f287,f308,f295,f291])).
% 0.22/0.59  fof(f287,plain,(
% 0.22/0.59    spl10_5 <=> r2_hidden(sK7(sK6,sK5),sK3)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.59  fof(f306,plain,(
% 0.22/0.59    ~r1_tarski(k1_relat_1(sK5),sK3) | sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | spl10_5),
% 0.22/0.59    inference(inner_rewriting,[],[f305])).
% 0.22/0.59  fof(f305,plain,(
% 0.22/0.59    ~r1_tarski(k1_relat_1(sK6),sK3) | sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | spl10_5),
% 0.22/0.59    inference(subsumption_resolution,[],[f304,f101])).
% 0.22/0.59  fof(f101,plain,(
% 0.22/0.59    v1_relat_1(sK6)),
% 0.22/0.59    inference(resolution,[],[f76,f58])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.59  fof(f304,plain,(
% 0.22/0.59    ~r1_tarski(k1_relat_1(sK6),sK3) | sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK6) | spl10_5),
% 0.22/0.59    inference(subsumption_resolution,[],[f303,f56])).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    v1_funct_1(sK6)),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f303,plain,(
% 0.22/0.59    ~r1_tarski(k1_relat_1(sK6),sK3) | sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl10_5),
% 0.22/0.59    inference(subsumption_resolution,[],[f302,f100])).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    v1_relat_1(sK5)),
% 0.22/0.59    inference(resolution,[],[f76,f55])).
% 0.22/0.59  fof(f302,plain,(
% 0.22/0.59    ~r1_tarski(k1_relat_1(sK6),sK3) | sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl10_5),
% 0.22/0.59    inference(subsumption_resolution,[],[f300,f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    v1_funct_1(sK5)),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f300,plain,(
% 0.22/0.59    ~r1_tarski(k1_relat_1(sK6),sK3) | sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl10_5),
% 0.22/0.59    inference(resolution,[],[f299,f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f36])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.59  fof(f299,plain,(
% 0.22/0.59    ( ! [X0] : (~r2_hidden(sK7(sK6,sK5),X0) | ~r1_tarski(X0,sK3)) ) | spl10_5),
% 0.22/0.59    inference(resolution,[],[f289,f70])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(rectify,[],[f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(nnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.59  fof(f289,plain,(
% 0.22/0.59    ~r2_hidden(sK7(sK6,sK5),sK3) | spl10_5),
% 0.22/0.59    inference(avatar_component_clause,[],[f287])).
% 0.22/0.59  fof(f298,plain,(
% 0.22/0.59    ~spl10_5 | ~spl10_6 | spl10_7),
% 0.22/0.59    inference(avatar_split_clause,[],[f285,f295,f291,f287])).
% 0.22/0.59  fof(f285,plain,(
% 0.22/0.59    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~r2_hidden(sK7(sK6,sK5),sK3)),
% 0.22/0.59    inference(subsumption_resolution,[],[f284,f100])).
% 0.22/0.59  fof(f284,plain,(
% 0.22/0.59    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~r2_hidden(sK7(sK6,sK5),sK3)),
% 0.22/0.59    inference(subsumption_resolution,[],[f283,f53])).
% 0.22/0.59  fof(f283,plain,(
% 0.22/0.59    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~r2_hidden(sK7(sK6,sK5),sK3)),
% 0.22/0.59    inference(equality_resolution,[],[f279])).
% 0.22/0.59  fof(f279,plain,(
% 0.22/0.59    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7(sK6,X0),sK3)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f278,f101])).
% 0.22/0.59  fof(f278,plain,(
% 0.22/0.59    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK6) | ~r2_hidden(sK7(sK6,X0),sK3)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f274,f56])).
% 0.22/0.59  fof(f274,plain,(
% 0.22/0.59    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~r2_hidden(sK7(sK6,X0),sK3)) )),
% 0.22/0.59    inference(superposition,[],[f63,f59])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f36])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (8079)------------------------------
% 0.22/0.59  % (8079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (8079)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (8079)Memory used [KB]: 6524
% 0.22/0.59  % (8079)Time elapsed: 0.182 s
% 0.22/0.59  % (8079)------------------------------
% 0.22/0.59  % (8079)------------------------------
% 0.22/0.59  % (8051)Success in time 0.219 s
%------------------------------------------------------------------------------
