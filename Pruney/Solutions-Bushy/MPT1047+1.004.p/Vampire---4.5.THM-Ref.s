%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1047+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:10 EST 2020

% Result     : Theorem 4.19s
% Output     : Refutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 710 expanded)
%              Number of leaves         :   28 ( 222 expanded)
%              Depth                    :   28
%              Number of atoms          :  678 (3469 expanded)
%              Number of equality atoms :   94 ( 532 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2839,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f412,f480,f669,f1125,f1252,f2838])).

fof(f2838,plain,(
    ~ spl13_30 ),
    inference(avatar_contradiction_clause,[],[f2837])).

fof(f2837,plain,
    ( $false
    | ~ spl13_30 ),
    inference(subsumption_resolution,[],[f2836,f227])).

fof(f227,plain,(
    sP4(sK7,sK5,k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f223,f63])).

fof(f63,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k5_partfun1(sK5,k1_tarski(sK6),sK7) != k1_tarski(sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    & v1_funct_2(sK8,sK5,k1_tarski(sK6))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f15,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK5,k1_tarski(sK6),sK7)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
          & v1_funct_2(X3,sK5,k1_tarski(sK6))
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK5,k1_tarski(sK6),sK7)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
        & v1_funct_2(X3,sK5,k1_tarski(sK6))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK5,k1_tarski(sK6),sK7) != k1_tarski(sK8)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      & v1_funct_2(sK8,sK5,k1_tarski(sK6))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f223,plain,
    ( sP4(sK7,sK5,k1_tarski(sK6))
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[],[f97,f64])).

fof(f64,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP4(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f26,f38,f37,f36])).

fof(f36,plain,(
    ! [X2,X0,X4,X1] :
      ( sP2(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f37,plain,(
    ! [X1,X0,X2,X3] :
      ( sP3(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP2(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP3(X1,X0,X2,X3) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(f2836,plain,
    ( ~ sP4(sK7,sK5,k1_tarski(sK6))
    | ~ spl13_30 ),
    inference(subsumption_resolution,[],[f2833,f68])).

fof(f68,plain,(
    k5_partfun1(sK5,k1_tarski(sK6),sK7) != k1_tarski(sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f2833,plain,
    ( k5_partfun1(sK5,k1_tarski(sK6),sK7) = k1_tarski(sK8)
    | ~ sP4(sK7,sK5,k1_tarski(sK6))
    | ~ spl13_30 ),
    inference(resolution,[],[f2832,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) = X3
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP3(X2,X1,X0,X3) )
          & ( sP3(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP3(X1,X0,X2,X3) )
          & ( sP3(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f2832,plain,
    ( sP3(k1_tarski(sK6),sK5,sK7,k1_tarski(sK8))
    | ~ spl13_30 ),
    inference(subsumption_resolution,[],[f2831,f108])).

fof(f108,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f102,f103])).

fof(f103,plain,(
    ! [X0] : sP0(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f2,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f102,plain,(
    ! [X3,X1] :
      ( ~ sP0(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK10(X0,X1) != X0
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sK10(X0,X1) = X0
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK10(X0,X1) != X0
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sK10(X0,X1) = X0
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f2831,plain,
    ( sP3(k1_tarski(sK6),sK5,sK7,k1_tarski(sK8))
    | ~ r2_hidden(sK8,k1_tarski(sK8))
    | ~ spl13_30 ),
    inference(subsumption_resolution,[],[f2828,f1124])).

fof(f1124,plain,
    ( sP2(sK7,sK5,sK8,k1_tarski(sK6))
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1122,plain,
    ( spl13_30
  <=> sP2(sK7,sK5,sK8,k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f2828,plain,
    ( ~ sP2(sK7,sK5,sK8,k1_tarski(sK6))
    | sP3(k1_tarski(sK6),sK5,sK7,k1_tarski(sK8))
    | ~ r2_hidden(sK8,k1_tarski(sK8)) ),
    inference(superposition,[],[f90,f2803])).

fof(f2803,plain,(
    sK8 = sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(sK8)) ),
    inference(subsumption_resolution,[],[f2802,f68])).

fof(f2802,plain,
    ( sK8 = sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(sK8))
    | k5_partfun1(sK5,k1_tarski(sK6),sK7) = k1_tarski(sK8) ),
    inference(equality_resolution,[],[f2798])).

fof(f2798,plain,(
    ! [X0] :
      ( sK8 != X0
      | sK8 = sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(X0))
      | k1_tarski(X0) = k5_partfun1(sK5,k1_tarski(sK6),sK7) ) ),
    inference(equality_factoring,[],[f2254])).

fof(f2254,plain,(
    ! [X0] :
      ( sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(X0)) = X0
      | sK8 = sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(X0))
      | k1_tarski(X0) = k5_partfun1(sK5,k1_tarski(sK6),sK7) ) ),
    inference(subsumption_resolution,[],[f2251,f227])).

fof(f2251,plain,(
    ! [X0] :
      ( sK8 = sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(X0))
      | sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k5_partfun1(sK5,k1_tarski(sK6),sK7)
      | ~ sP4(sK7,sK5,k1_tarski(sK6)) ) ),
    inference(resolution,[],[f1549,f86])).

fof(f1549,plain,(
    ! [X3] :
      ( sP3(k1_tarski(sK6),sK5,sK7,k1_tarski(X3))
      | sK8 = sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(X3))
      | sK11(k1_tarski(sK6),sK5,sK7,k1_tarski(X3)) = X3 ) ),
    inference(resolution,[],[f1517,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f73,f103])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1517,plain,(
    ! [X2] :
      ( r2_hidden(sK11(k1_tarski(sK6),sK5,sK7,X2),X2)
      | sP3(k1_tarski(sK6),sK5,sK7,X2)
      | sK8 = sK11(k1_tarski(sK6),sK5,sK7,X2) ) ),
    inference(resolution,[],[f762,f1040])).

fof(f1040,plain,(
    ! [X0] :
      ( ~ sP1(k1_tarski(sK6),sK5,X0)
      | sK8 = X0 ) ),
    inference(duplicate_literal_removal,[],[f1032])).

fof(f1032,plain,(
    ! [X0] :
      ( ~ sP1(k1_tarski(sK6),sK5,X0)
      | sK8 = X0
      | ~ sP1(k1_tarski(sK6),sK5,X0) ) ),
    inference(resolution,[],[f1029,f699])).

fof(f699,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK5,k1_tarski(sK6),X0,sK8)
      | sK8 = X0
      | ~ sP1(k1_tarski(sK6),sK5,X0) ) ),
    inference(resolution,[],[f679,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
      | ~ sP1(X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
      | ~ sP1(X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f679,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | sK8 = X5
      | ~ r2_relset_1(sK5,k1_tarski(sK6),X5,sK8) ) ),
    inference(resolution,[],[f100,f67])).

fof(f67,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1029,plain,(
    ! [X0] :
      ( r2_relset_1(sK5,k1_tarski(sK6),X0,sK8)
      | ~ sP1(k1_tarski(sK6),sK5,X0) ) ),
    inference(subsumption_resolution,[],[f1028,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1028,plain,(
    ! [X0] :
      ( r2_relset_1(sK5,k1_tarski(sK6),X0,sK8)
      | ~ v1_funct_1(X0)
      | ~ sP1(k1_tarski(sK6),sK5,X0) ) ),
    inference(subsumption_resolution,[],[f1023,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v1_funct_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1023,plain,(
    ! [X0] :
      ( r2_relset_1(sK5,k1_tarski(sK6),X0,sK8)
      | ~ v1_funct_2(X0,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(X0)
      | ~ sP1(k1_tarski(sK6),sK5,X0) ) ),
    inference(resolution,[],[f987,f83])).

fof(f987,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | r2_relset_1(sK5,k1_tarski(sK6),X5,sK8)
      | ~ v1_funct_2(X5,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f986,f65])).

fof(f65,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f986,plain,(
    ! [X5] :
      ( r2_relset_1(sK5,k1_tarski(sK6),X5,sK8)
      | ~ v1_funct_1(sK8)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(X5,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f981,f66])).

fof(f66,plain,(
    v1_funct_2(sK8,sK5,k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f981,plain,(
    ! [X5] :
      ( r2_relset_1(sK5,k1_tarski(sK6),X5,sK8)
      | ~ v1_funct_2(sK8,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(sK8)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(X5,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f80,f67])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

fof(f762,plain,(
    ! [X8] :
      ( sP1(k1_tarski(sK6),sK5,sK11(k1_tarski(sK6),sK5,sK7,X8))
      | r2_hidden(sK11(k1_tarski(sK6),sK5,sK7,X8),X8)
      | sP3(k1_tarski(sK6),sK5,sK7,X8) ) ),
    inference(resolution,[],[f89,f508])).

fof(f508,plain,(
    ! [X4] :
      ( ~ sP2(sK7,sK5,X4,k1_tarski(sK6))
      | sP1(k1_tarski(sK6),sK5,X4) ) ),
    inference(subsumption_resolution,[],[f503,f63])).

fof(f503,plain,(
    ! [X4] :
      ( sP1(k1_tarski(sK6),sK5,X4)
      | ~ v1_funct_1(sK7)
      | ~ sP2(sK7,sK5,X4,k1_tarski(sK6)) ) ),
    inference(resolution,[],[f403,f64])).

fof(f403,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | sP1(X0,X1,X2)
      | ~ v1_funct_1(X3)
      | ~ sP2(X3,X1,X2,X0) ) ),
    inference(subsumption_resolution,[],[f400,f97])).

fof(f400,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X3)
      | ~ sP2(X3,X1,X2,X0)
      | ~ sP4(X3,X1,X0) ) ),
    inference(resolution,[],[f84,f232])).

fof(f232,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k5_partfun1(X1,X3,X0))
      | ~ sP2(X0,X1,X2,X3)
      | ~ sP4(X0,X1,X3) ) ),
    inference(resolution,[],[f88,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP4(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ sP2(X2,X1,X5,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ~ sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
            | ~ r2_hidden(sK11(X0,X1,X2,X3),X3) )
          & ( sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
            | r2_hidden(sK11(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X2,X1,X5,X0) )
            & ( sP2(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f55,f56])).

fof(f56,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP2(X2,X1,X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP2(X2,X1,X4,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
          | ~ r2_hidden(sK11(X0,X1,X2,X3),X3) )
        & ( sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
          | r2_hidden(sK11(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X2,X1,X4,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X2,X1,X4,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X2,X1,X5,X0) )
            & ( sP2(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP3(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X2,X0,X4,X1)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP2(X2,X0,X4,X1) )
            & ( sP2(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | sP1(X1,X0,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP1(X1,X0,X3)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f24,f34])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
      | r2_hidden(sK11(X0,X1,X2,X3),X3)
      | sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
      | sP3(X0,X1,X2,X3)
      | ~ r2_hidden(sK11(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1252,plain,
    ( ~ spl13_7
    | ~ spl13_18 ),
    inference(avatar_contradiction_clause,[],[f1251])).

fof(f1251,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f1245,f900])).

fof(f900,plain,(
    r1_partfun1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f888,f63])).

fof(f888,plain,
    ( r1_partfun1(sK7,sK8)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[],[f870,f64])).

fof(f870,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | r1_partfun1(X5,sK8)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f865,f65])).

fof(f865,plain,(
    ! [X5] :
      ( r1_partfun1(X5,sK8)
      | ~ v1_funct_1(sK8)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f98,f67])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f1245,plain,
    ( ~ r1_partfun1(sK7,sK8)
    | ~ spl13_7
    | ~ spl13_18 ),
    inference(resolution,[],[f1244,f608])).

fof(f608,plain,
    ( ! [X5] :
        ( sP2(X5,sK5,sK8,k1_tarski(sK6))
        | ~ r1_partfun1(X5,sK8) )
    | ~ spl13_7 ),
    inference(subsumption_resolution,[],[f607,f65])).

fof(f607,plain,
    ( ! [X5] :
        ( ~ r1_partfun1(X5,sK8)
        | sP2(X5,sK5,sK8,k1_tarski(sK6))
        | ~ v1_funct_1(sK8) )
    | ~ spl13_7 ),
    inference(subsumption_resolution,[],[f602,f411])).

fof(f411,plain,
    ( v1_partfun1(sK8,sK5)
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl13_7
  <=> v1_partfun1(sK8,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f602,plain,(
    ! [X5] :
      ( ~ r1_partfun1(X5,sK8)
      | ~ v1_partfun1(sK8,sK5)
      | sP2(X5,sK5,sK8,k1_tarski(sK6))
      | ~ v1_funct_1(sK8) ) ),
    inference(resolution,[],[f105,f67])).

fof(f105,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | sP2(X0,X1,X4,X3)
      | ~ v1_funct_1(X4) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ( r1_partfun1(X0,sK12(X0,X1,X2,X3))
          & v1_partfun1(sK12(X0,X1,X2,X3),X1)
          & sK12(X0,X1,X2,X3) = X2
          & m1_subset_1(sK12(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(sK12(X0,X1,X2,X3)) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f59,f60])).

fof(f60,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_partfun1(X0,X5)
          & v1_partfun1(X5,X1)
          & X2 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(X5) )
     => ( r1_partfun1(X0,sK12(X0,X1,X2,X3))
        & v1_partfun1(sK12(X0,X1,X2,X3),X1)
        & sK12(X0,X1,X2,X3) = X2
        & m1_subset_1(sK12(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & v1_funct_1(sK12(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ? [X5] :
            ( r1_partfun1(X0,X5)
            & v1_partfun1(X5,X1)
            & X2 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            & v1_funct_1(X5) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X4,X1] :
      ( ( sP2(X2,X0,X4,X1)
        | ! [X5] :
            ( ~ r1_partfun1(X2,X5)
            | ~ v1_partfun1(X5,X0)
            | X4 != X5
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_1(X5) ) )
      & ( ? [X5] :
            ( r1_partfun1(X2,X5)
            & v1_partfun1(X5,X0)
            & X4 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X5) )
        | ~ sP2(X2,X0,X4,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f1244,plain,
    ( ! [X0] : ~ sP2(sK7,sK5,X0,k1_tarski(sK6))
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f1240,f227])).

fof(f1240,plain,
    ( ! [X0] :
        ( ~ sP2(sK7,sK5,X0,k1_tarski(sK6))
        | ~ sP4(sK7,sK5,k1_tarski(sK6)) )
    | ~ spl13_18 ),
    inference(resolution,[],[f1228,f232])).

fof(f1228,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_partfun1(sK5,k1_tarski(sK6),sK7))
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f1212,f668])).

fof(f668,plain,
    ( v1_xboole_0(k5_partfun1(sK5,k1_tarski(sK6),sK7))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f666])).

fof(f666,plain,
    ( spl13_18
  <=> v1_xboole_0(k5_partfun1(sK5,k1_tarski(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f1212,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_partfun1(sK5,k1_tarski(sK6),sK7))
        | ~ v1_xboole_0(k5_partfun1(sK5,k1_tarski(sK6),sK7)) )
    | ~ spl13_18 ),
    inference(superposition,[],[f117,f1147])).

fof(f1147,plain,
    ( k5_partfun1(sK5,k1_tarski(sK6),sK7) = sK9(k1_zfmisc_1(k5_partfun1(sK5,k1_tarski(sK6),sK7)))
    | ~ spl13_18 ),
    inference(resolution,[],[f1127,f668])).

fof(f1127,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | k5_partfun1(sK5,k1_tarski(sK6),sK7) = sK9(k1_zfmisc_1(X1)) )
    | ~ spl13_18 ),
    inference(resolution,[],[f668,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | sK9(k1_zfmisc_1(X0)) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f120,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f120,plain,(
    ! [X0] :
      ( v1_xboole_0(sK9(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f117,f110])).

fof(f110,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f72,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f4,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK9(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f99,f69])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f1125,plain,
    ( spl13_18
    | spl13_30
    | ~ spl13_17 ),
    inference(avatar_split_clause,[],[f1091,f662,f1122,f666])).

fof(f662,plain,
    ( spl13_17
  <=> sP1(k1_tarski(sK6),sK5,sK9(k5_partfun1(sK5,k1_tarski(sK6),sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f1091,plain,
    ( sP2(sK7,sK5,sK8,k1_tarski(sK6))
    | v1_xboole_0(k5_partfun1(sK5,k1_tarski(sK6),sK7))
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f1081,f227])).

fof(f1081,plain,
    ( sP2(sK7,sK5,sK8,k1_tarski(sK6))
    | ~ sP4(sK7,sK5,k1_tarski(sK6))
    | v1_xboole_0(k5_partfun1(sK5,k1_tarski(sK6),sK7))
    | ~ spl13_17 ),
    inference(superposition,[],[f257,f1042])).

fof(f1042,plain,
    ( sK8 = sK9(k5_partfun1(sK5,k1_tarski(sK6),sK7))
    | ~ spl13_17 ),
    inference(resolution,[],[f1040,f664])).

fof(f664,plain,
    ( sP1(k1_tarski(sK6),sK5,sK9(k5_partfun1(sK5,k1_tarski(sK6),sK7)))
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f662])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,sK9(k5_partfun1(X1,X2,X0)),X2)
      | ~ sP4(X0,X1,X2)
      | v1_xboole_0(k5_partfun1(X1,X2,X0)) ) ),
    inference(resolution,[],[f231,f110])).

fof(f231,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
      | sP2(X3,X1,X0,X2)
      | ~ sP4(X3,X1,X2) ) ),
    inference(resolution,[],[f87,f104])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP2(X2,X1,X5,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f669,plain,
    ( spl13_17
    | spl13_18 ),
    inference(avatar_split_clause,[],[f659,f666,f662])).

fof(f659,plain,
    ( v1_xboole_0(k5_partfun1(sK5,k1_tarski(sK6),sK7))
    | sP1(k1_tarski(sK6),sK5,sK9(k5_partfun1(sK5,k1_tarski(sK6),sK7))) ),
    inference(subsumption_resolution,[],[f656,f227])).

fof(f656,plain,
    ( ~ sP4(sK7,sK5,k1_tarski(sK6))
    | v1_xboole_0(k5_partfun1(sK5,k1_tarski(sK6),sK7))
    | sP1(k1_tarski(sK6),sK5,sK9(k5_partfun1(sK5,k1_tarski(sK6),sK7))) ),
    inference(resolution,[],[f257,f508])).

fof(f480,plain,(
    ~ spl13_6 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl13_6 ),
    inference(resolution,[],[f472,f108])).

fof(f472,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_tarski(sK6))
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f469,f407])).

fof(f407,plain,
    ( v1_xboole_0(k1_tarski(sK6))
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl13_6
  <=> v1_xboole_0(k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f469,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_tarski(sK6))
        | ~ v1_xboole_0(k1_tarski(sK6)) )
    | ~ spl13_6 ),
    inference(superposition,[],[f117,f435])).

fof(f435,plain,
    ( k1_tarski(sK6) = sK9(k1_zfmisc_1(k1_tarski(sK6)))
    | ~ spl13_6 ),
    inference(resolution,[],[f415,f407])).

fof(f415,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | k1_tarski(sK6) = sK9(k1_zfmisc_1(X2)) )
    | ~ spl13_6 ),
    inference(resolution,[],[f407,f121])).

fof(f412,plain,
    ( spl13_6
    | spl13_7 ),
    inference(avatar_split_clause,[],[f399,f409,f405])).

fof(f399,plain,
    ( v1_partfun1(sK8,sK5)
    | v1_xboole_0(k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f398,f65])).

fof(f398,plain,
    ( ~ v1_funct_1(sK8)
    | v1_partfun1(sK8,sK5)
    | v1_xboole_0(k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f392,f66])).

fof(f392,plain,
    ( ~ v1_funct_2(sK8,sK5,k1_tarski(sK6))
    | ~ v1_funct_1(sK8)
    | v1_partfun1(sK8,sK5)
    | v1_xboole_0(k1_tarski(sK6)) ),
    inference(resolution,[],[f71,f67])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

%------------------------------------------------------------------------------
