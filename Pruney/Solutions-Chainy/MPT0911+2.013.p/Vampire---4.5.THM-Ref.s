%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:30 EST 2020

% Result     : Theorem 2.39s
% Output     : Refutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 427 expanded)
%              Number of leaves         :   38 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  562 (1902 expanded)
%              Number of equality atoms :  141 ( 776 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f214,f524,f627,f855,f874,f958,f982,f983,f993,f1001,f2974,f3260,f3284,f3313,f3342])).

fof(f3342,plain,
    ( ~ spl16_9
    | ~ spl16_22 ),
    inference(avatar_contradiction_clause,[],[f3341])).

fof(f3341,plain,
    ( $false
    | ~ spl16_9
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f399,f692])).

fof(f692,plain,
    ( ! [X0,X1] : ~ sP1(k1_mcart_1(sK8),X0,X1)
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f691])).

fof(f691,plain,
    ( spl16_22
  <=> ! [X1,X0] : ~ sP1(k1_mcart_1(sK8),X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f399,plain,
    ( sP1(k1_mcart_1(sK8),sK5,sK4)
    | ~ spl16_9 ),
    inference(resolution,[],[f387,f227])).

fof(f227,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK4,sK5))
    | ~ spl16_9 ),
    inference(resolution,[],[f88,f209])).

fof(f209,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl16_9 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl16_9
  <=> r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f387,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sP1(X0,X2,X1) ) ),
    inference(resolution,[],[f90,f130])).

fof(f130,plain,(
    ! [X0,X1] : sP2(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f34,f33])).

fof(f33,plain,(
    ! [X3,X1,X0] :
      ( sP1(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(sK11(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( sP1(sK11(X0,X1,X2),X1,X0)
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(sK11(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( sP1(sK11(X0,X1,X2),X1,X0)
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X3,X1,X0) )
            & ( sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f3313,plain,
    ( spl16_22
    | ~ spl16_23
    | ~ spl16_9
    | ~ spl16_15
    | spl16_16
    | ~ spl16_39
    | ~ spl16_61 ),
    inference(avatar_split_clause,[],[f3312,f2966,f910,f521,f517,f207,f694,f691])).

fof(f694,plain,
    ( spl16_23
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_23])])).

fof(f517,plain,
    ( spl16_15
  <=> sP3(sK8,sK6,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_15])])).

fof(f521,plain,
    ( spl16_16
  <=> sK7 = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).

fof(f910,plain,
    ( spl16_39
  <=> sK8 = k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).

fof(f2966,plain,
    ( spl16_61
  <=> m1_subset_1(k2_mcart_1(sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_61])])).

fof(f3312,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4)
        | ~ sP1(k1_mcart_1(sK8),X16,X17) )
    | ~ spl16_9
    | ~ spl16_15
    | spl16_16
    | ~ spl16_39
    | ~ spl16_61 ),
    inference(subsumption_resolution,[],[f3311,f2968])).

fof(f2968,plain,
    ( m1_subset_1(k2_mcart_1(sK8),sK6)
    | ~ spl16_61 ),
    inference(avatar_component_clause,[],[f2966])).

fof(f3311,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4)
        | ~ m1_subset_1(k2_mcart_1(sK8),sK6)
        | ~ sP1(k1_mcart_1(sK8),X16,X17) )
    | ~ spl16_9
    | ~ spl16_15
    | spl16_16
    | ~ spl16_39 ),
    inference(subsumption_resolution,[],[f1252,f3253])).

fof(f3253,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK5)
    | ~ spl16_15 ),
    inference(subsumption_resolution,[],[f3235,f518])).

fof(f518,plain,
    ( sP3(sK8,sK6,sK5,sK4)
    | ~ spl16_15 ),
    inference(avatar_component_clause,[],[f517])).

fof(f3235,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK5)
    | ~ sP3(sK8,sK6,sK5,sK4) ),
    inference(resolution,[],[f641,f116])).

fof(f116,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f67,plain,(
    m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( sK7 != k7_mcart_1(sK4,sK5,sK6,sK8)
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK7 = X7
                | k3_mcart_1(X5,X6,X7) != sK8
                | ~ m1_subset_1(X7,sK6) )
            | ~ m1_subset_1(X6,sK5) )
        | ~ m1_subset_1(X5,sK4) )
    & m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f21,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK7 != k7_mcart_1(sK4,sK5,sK6,sK8)
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK7 = X7
                  | k3_mcart_1(X5,X6,X7) != sK8
                  | ~ m1_subset_1(X7,sK6) )
              | ~ m1_subset_1(X6,sK5) )
          | ~ m1_subset_1(X5,sK4) )
      & m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f641,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1)
      | ~ sP3(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f122,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP3(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP3(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f109,f87])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f1252,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK5)
        | ~ m1_subset_1(k2_mcart_1(sK8),sK6)
        | ~ sP1(k1_mcart_1(sK8),X16,X17) )
    | ~ spl16_9
    | spl16_16
    | ~ spl16_39 ),
    inference(forward_demodulation,[],[f1251,f668])).

fof(f668,plain,
    ( k1_mcart_1(k1_mcart_1(sK8)) = sK14(k1_mcart_1(sK8))
    | ~ spl16_9 ),
    inference(resolution,[],[f227,f431])).

fof(f431,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k1_mcart_1(X0) = sK14(X0) ) ),
    inference(superposition,[],[f80,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK14(X0),sK15(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK14(X0),sK15(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f27,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK14(X0),sK15(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f80,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f1251,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK5)
        | ~ m1_subset_1(k2_mcart_1(sK8),sK6)
        | ~ m1_subset_1(sK14(k1_mcart_1(sK8)),sK4)
        | ~ sP1(k1_mcart_1(sK8),X16,X17) )
    | ~ spl16_9
    | spl16_16
    | ~ spl16_39 ),
    inference(forward_demodulation,[],[f1250,f669])).

fof(f669,plain,
    ( k2_mcart_1(k1_mcart_1(sK8)) = sK15(k1_mcart_1(sK8))
    | ~ spl16_9 ),
    inference(resolution,[],[f227,f432])).

fof(f432,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
      | k2_mcart_1(X3) = sK15(X3) ) ),
    inference(superposition,[],[f81,f108])).

fof(f81,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f1250,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(k2_mcart_1(sK8),sK6)
        | ~ m1_subset_1(sK15(k1_mcart_1(sK8)),sK5)
        | ~ m1_subset_1(sK14(k1_mcart_1(sK8)),sK4)
        | ~ sP1(k1_mcart_1(sK8),X16,X17) )
    | spl16_16
    | ~ spl16_39 ),
    inference(subsumption_resolution,[],[f1241,f523])).

fof(f523,plain,
    ( sK7 != k2_mcart_1(sK8)
    | spl16_16 ),
    inference(avatar_component_clause,[],[f521])).

fof(f1241,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(k2_mcart_1(sK8),sK6)
        | ~ m1_subset_1(sK15(k1_mcart_1(sK8)),sK5)
        | ~ m1_subset_1(sK14(k1_mcart_1(sK8)),sK4)
        | sK7 = k2_mcart_1(sK8)
        | ~ sP1(k1_mcart_1(sK8),X16,X17) )
    | ~ spl16_39 ),
    inference(trivial_inequality_removal,[],[f1240])).

fof(f1240,plain,
    ( ! [X17,X16] :
        ( sK8 != sK8
        | ~ m1_subset_1(k2_mcart_1(sK8),sK6)
        | ~ m1_subset_1(sK15(k1_mcart_1(sK8)),sK5)
        | ~ m1_subset_1(sK14(k1_mcart_1(sK8)),sK4)
        | sK7 = k2_mcart_1(sK8)
        | ~ sP1(k1_mcart_1(sK8),X16,X17) )
    | ~ spl16_39 ),
    inference(superposition,[],[f571,f912])).

fof(f912,plain,
    ( sK8 = k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))
    | ~ spl16_39 ),
    inference(avatar_component_clause,[],[f910])).

fof(f571,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8 != k4_tarski(X1,X0)
      | ~ m1_subset_1(X0,sK6)
      | ~ m1_subset_1(sK15(X1),sK5)
      | ~ m1_subset_1(sK14(X1),sK4)
      | sK7 = X0
      | ~ sP1(X1,X2,X3) ) ),
    inference(resolution,[],[f435,f392])).

fof(f392,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(resolution,[],[f91,f130])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f435,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(X16,k2_zfmisc_1(X18,X19))
      | sK7 = X17
      | ~ m1_subset_1(X17,sK6)
      | ~ m1_subset_1(sK15(X16),sK5)
      | ~ m1_subset_1(sK14(X16),sK4)
      | sK8 != k4_tarski(X16,X17) ) ),
    inference(superposition,[],[f115,f108])).

fof(f115,plain,(
    ! [X6,X7,X5] :
      ( sK8 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK7 = X7
      | ~ m1_subset_1(X7,sK6)
      | ~ m1_subset_1(X6,sK5)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f68,plain,(
    ! [X6,X7,X5] :
      ( sK7 = X7
      | k3_mcart_1(X5,X6,X7) != sK8
      | ~ m1_subset_1(X7,sK6)
      | ~ m1_subset_1(X6,sK5)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3284,plain,
    ( spl16_23
    | ~ spl16_15 ),
    inference(avatar_split_clause,[],[f3283,f517,f694])).

fof(f3283,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4)
    | ~ spl16_15 ),
    inference(subsumption_resolution,[],[f3265,f518])).

fof(f3265,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4)
    | ~ sP3(sK8,sK6,sK5,sK4) ),
    inference(resolution,[],[f656,f116])).

fof(f656,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0)
      | ~ sP3(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f123,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f110,f87])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f3260,plain,
    ( spl16_34
    | spl16_39
    | ~ spl16_9 ),
    inference(avatar_split_clause,[],[f3259,f207,f910,f836])).

fof(f836,plain,
    ( spl16_34
  <=> ! [X1,X0] : ~ r2_hidden(sK8,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).

fof(f3259,plain,
    ( ! [X0,X1] :
        ( sK8 = k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))
        | ~ r2_hidden(sK8,k2_zfmisc_1(X0,X1)) )
    | ~ spl16_9 ),
    inference(forward_demodulation,[],[f3258,f781])).

fof(f781,plain,
    ( k2_mcart_1(sK8) = sK15(sK8)
    | ~ spl16_9 ),
    inference(resolution,[],[f209,f432])).

fof(f3258,plain,
    ( ! [X0,X1] :
        ( sK8 = k4_tarski(k1_mcart_1(sK8),sK15(sK8))
        | ~ r2_hidden(sK8,k2_zfmisc_1(X0,X1)) )
    | ~ spl16_9 ),
    inference(superposition,[],[f108,f780])).

fof(f780,plain,
    ( k1_mcart_1(sK8) = sK14(sK8)
    | ~ spl16_9 ),
    inference(resolution,[],[f209,f431])).

fof(f2974,plain,
    ( spl16_61
    | ~ spl16_15 ),
    inference(avatar_split_clause,[],[f2961,f517,f2966])).

fof(f2961,plain,
    ( m1_subset_1(k2_mcart_1(sK8),sK6)
    | ~ spl16_15 ),
    inference(subsumption_resolution,[],[f2943,f518])).

fof(f2943,plain,
    ( m1_subset_1(k2_mcart_1(sK8),sK6)
    | ~ sP3(sK8,sK6,sK5,sK4) ),
    inference(resolution,[],[f734,f116])).

fof(f734,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k2_mcart_1(X3),X2)
      | ~ sP3(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f124,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f111,f87])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f1001,plain,(
    ~ spl16_38 ),
    inference(avatar_contradiction_clause,[],[f1000])).

fof(f1000,plain,
    ( $false
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f995,f70])).

fof(f70,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f39])).

fof(f995,plain,
    ( k1_xboole_0 = sK5
    | ~ spl16_38 ),
    inference(resolution,[],[f873,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP0(sK10(X0),X0)
        & r2_hidden(sK10(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f32,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK10(X0),X0)
        & r2_hidden(sK10(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f873,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK5)
    | ~ spl16_38 ),
    inference(avatar_component_clause,[],[f872])).

fof(f872,plain,
    ( spl16_38
  <=> ! [X1] : ~ r2_hidden(X1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).

fof(f993,plain,(
    ~ spl16_37 ),
    inference(avatar_contradiction_clause,[],[f992])).

fof(f992,plain,
    ( $false
    | ~ spl16_37 ),
    inference(subsumption_resolution,[],[f987,f69])).

fof(f69,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f987,plain,
    ( k1_xboole_0 = sK4
    | ~ spl16_37 ),
    inference(resolution,[],[f870,f77])).

fof(f870,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK4)
    | ~ spl16_37 ),
    inference(avatar_component_clause,[],[f869])).

fof(f869,plain,
    ( spl16_37
  <=> ! [X2] : ~ r2_hidden(X2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_37])])).

fof(f983,plain,
    ( spl16_32
    | ~ spl16_34 ),
    inference(avatar_split_clause,[],[f927,f836,f806])).

fof(f806,plain,
    ( spl16_32
  <=> ! [X1,X0] : ~ sP1(sK8,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_32])])).

fof(f927,plain,
    ( ! [X0,X1] : ~ sP1(sK8,X0,X1)
    | ~ spl16_34 ),
    inference(resolution,[],[f837,f392])).

fof(f837,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK8,k2_zfmisc_1(X0,X1))
    | ~ spl16_34 ),
    inference(avatar_component_clause,[],[f836])).

fof(f982,plain,
    ( ~ spl16_9
    | ~ spl16_32 ),
    inference(avatar_contradiction_clause,[],[f981])).

fof(f981,plain,
    ( $false
    | ~ spl16_9
    | ~ spl16_32 ),
    inference(subsumption_resolution,[],[f397,f807])).

fof(f807,plain,
    ( ! [X0,X1] : ~ sP1(sK8,X0,X1)
    | ~ spl16_32 ),
    inference(avatar_component_clause,[],[f806])).

fof(f397,plain,
    ( sP1(sK8,sK6,k2_zfmisc_1(sK4,sK5))
    | ~ spl16_9 ),
    inference(resolution,[],[f387,f209])).

fof(f958,plain,(
    spl16_15 ),
    inference(avatar_split_clause,[],[f957,f517])).

fof(f957,plain,(
    sP3(sK8,sK6,sK5,sK4) ),
    inference(subsumption_resolution,[],[f956,f69])).

fof(f956,plain,
    ( sP3(sK8,sK6,sK5,sK4)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f955,f70])).

fof(f955,plain,
    ( sP3(sK8,sK6,sK5,sK4)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f935,f71])).

fof(f71,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f39])).

fof(f935,plain,
    ( sP3(sK8,sK6,sK5,sK4)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f121,f116])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP3(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f107,f87])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP3(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f26,f36])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f874,plain,
    ( spl16_37
    | spl16_38
    | ~ spl16_18 ),
    inference(avatar_split_clause,[],[f860,f625,f872,f869])).

fof(f625,plain,
    ( spl16_18
  <=> ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_18])])).

fof(f860,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,sK5)
        | ~ r2_hidden(X2,sK4) )
    | ~ spl16_18 ),
    inference(resolution,[],[f626,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f626,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK4,sK5))
    | ~ spl16_18 ),
    inference(avatar_component_clause,[],[f625])).

fof(f855,plain,(
    ~ spl16_17 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | ~ spl16_17 ),
    inference(subsumption_resolution,[],[f849,f71])).

fof(f849,plain,
    ( k1_xboole_0 = sK6
    | ~ spl16_17 ),
    inference(resolution,[],[f623,f77])).

fof(f623,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK6)
    | ~ spl16_17 ),
    inference(avatar_component_clause,[],[f622])).

fof(f622,plain,
    ( spl16_17
  <=> ! [X1] : ~ r2_hidden(X1,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_17])])).

fof(f627,plain,
    ( spl16_17
    | spl16_18
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f609,f211,f625,f622])).

fof(f211,plain,
    ( spl16_10
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f609,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(sK4,sK5))
        | ~ r2_hidden(X1,sK6) )
    | ~ spl16_10 ),
    inference(resolution,[],[f544,f213])).

fof(f213,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f211])).

fof(f544,plain,(
    ! [X30,X28,X29,X27] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X30,X28))
      | ~ r2_hidden(X29,X30)
      | ~ r2_hidden(X27,X28) ) ),
    inference(resolution,[],[f114,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK9(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f524,plain,
    ( ~ spl16_15
    | ~ spl16_16 ),
    inference(avatar_split_clause,[],[f515,f521,f517])).

fof(f515,plain,
    ( sK7 != k2_mcart_1(sK8)
    | ~ sP3(sK8,sK6,sK5,sK4) ),
    inference(superposition,[],[f72,f106])).

fof(f72,plain,(
    sK7 != k7_mcart_1(sK4,sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f214,plain,
    ( spl16_9
    | spl16_10 ),
    inference(avatar_split_clause,[],[f205,f211,f207])).

fof(f205,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(resolution,[],[f82,f116])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (15694)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (15685)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (15710)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (15705)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (15700)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (15686)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (15685)Refutation not found, incomplete strategy% (15685)------------------------------
% 0.21/0.51  % (15685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15702)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (15697)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (15695)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15684)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (15707)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (15688)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (15683)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (15692)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (15685)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15685)Memory used [KB]: 10746
% 0.21/0.52  % (15685)Time elapsed: 0.101 s
% 0.21/0.52  % (15685)------------------------------
% 0.21/0.52  % (15685)------------------------------
% 0.21/0.52  % (15689)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (15690)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (15711)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (15706)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (15693)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (15698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (15687)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (15696)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (15703)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (15699)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (15701)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (15712)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (15709)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (15691)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.55  % (15704)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % (15691)Refutation not found, incomplete strategy% (15691)------------------------------
% 1.35/0.55  % (15691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (15691)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (15691)Memory used [KB]: 10746
% 1.35/0.55  % (15691)Time elapsed: 0.140 s
% 1.35/0.55  % (15691)------------------------------
% 1.35/0.55  % (15691)------------------------------
% 1.35/0.55  % (15708)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.55  % (15703)Refutation not found, incomplete strategy% (15703)------------------------------
% 1.48/0.55  % (15703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (15703)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (15703)Memory used [KB]: 10746
% 1.48/0.55  % (15703)Time elapsed: 0.154 s
% 1.48/0.55  % (15703)------------------------------
% 1.48/0.55  % (15703)------------------------------
% 1.48/0.56  % (15705)Refutation not found, incomplete strategy% (15705)------------------------------
% 1.48/0.56  % (15705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (15705)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (15705)Memory used [KB]: 11129
% 1.48/0.56  % (15705)Time elapsed: 0.112 s
% 1.48/0.56  % (15705)------------------------------
% 1.48/0.56  % (15705)------------------------------
% 2.03/0.63  % (15713)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.39/0.69  % (15715)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.39/0.69  % (15716)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.39/0.71  % (15714)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.39/0.72  % (15710)Refutation found. Thanks to Tanya!
% 2.39/0.72  % SZS status Theorem for theBenchmark
% 2.39/0.73  % SZS output start Proof for theBenchmark
% 2.39/0.73  fof(f3343,plain,(
% 2.39/0.73    $false),
% 2.39/0.73    inference(avatar_sat_refutation,[],[f214,f524,f627,f855,f874,f958,f982,f983,f993,f1001,f2974,f3260,f3284,f3313,f3342])).
% 2.39/0.73  fof(f3342,plain,(
% 2.39/0.73    ~spl16_9 | ~spl16_22),
% 2.39/0.73    inference(avatar_contradiction_clause,[],[f3341])).
% 2.39/0.73  fof(f3341,plain,(
% 2.39/0.73    $false | (~spl16_9 | ~spl16_22)),
% 2.39/0.73    inference(subsumption_resolution,[],[f399,f692])).
% 2.39/0.73  fof(f692,plain,(
% 2.39/0.73    ( ! [X0,X1] : (~sP1(k1_mcart_1(sK8),X0,X1)) ) | ~spl16_22),
% 2.39/0.73    inference(avatar_component_clause,[],[f691])).
% 2.39/0.73  fof(f691,plain,(
% 2.39/0.73    spl16_22 <=> ! [X1,X0] : ~sP1(k1_mcart_1(sK8),X0,X1)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).
% 2.39/0.73  fof(f399,plain,(
% 2.39/0.73    sP1(k1_mcart_1(sK8),sK5,sK4) | ~spl16_9),
% 2.39/0.73    inference(resolution,[],[f387,f227])).
% 2.39/0.73  fof(f227,plain,(
% 2.39/0.73    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK4,sK5)) | ~spl16_9),
% 2.39/0.73    inference(resolution,[],[f88,f209])).
% 2.39/0.73  fof(f209,plain,(
% 2.39/0.73    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl16_9),
% 2.39/0.73    inference(avatar_component_clause,[],[f207])).
% 2.39/0.73  fof(f207,plain,(
% 2.39/0.73    spl16_9 <=> r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).
% 2.39/0.73  fof(f88,plain,(
% 2.39/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f25])).
% 2.39/0.73  fof(f25,plain,(
% 2.39/0.73    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.39/0.73    inference(ennf_transformation,[],[f13])).
% 2.39/0.73  fof(f13,axiom,(
% 2.39/0.73    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.39/0.73  fof(f387,plain,(
% 2.39/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sP1(X0,X2,X1)) )),
% 2.39/0.73    inference(resolution,[],[f90,f130])).
% 2.39/0.73  fof(f130,plain,(
% 2.39/0.73    ( ! [X0,X1] : (sP2(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 2.39/0.73    inference(equality_resolution,[],[f98])).
% 2.39/0.73  fof(f98,plain,(
% 2.39/0.73    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.39/0.73    inference(cnf_transformation,[],[f58])).
% 2.39/0.73  fof(f58,plain,(
% 2.39/0.73    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 2.39/0.73    inference(nnf_transformation,[],[f35])).
% 2.39/0.73  fof(f35,plain,(
% 2.39/0.73    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 2.39/0.73    inference(definition_folding,[],[f2,f34,f33])).
% 2.39/0.73  fof(f33,plain,(
% 2.39/0.73    ! [X3,X1,X0] : (sP1(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 2.39/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.39/0.73  fof(f34,plain,(
% 2.39/0.73    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X3,X1,X0)))),
% 2.39/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.39/0.73  fof(f2,axiom,(
% 2.39/0.73    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.39/0.73  fof(f90,plain,(
% 2.39/0.73    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X4,X1,X0)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f53])).
% 2.39/0.73  fof(f53,plain,(
% 2.39/0.73    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(sK11(X0,X1,X2),X1,X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sP1(sK11(X0,X1,X2),X1,X0) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 2.39/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f51,f52])).
% 2.39/0.73  fof(f52,plain,(
% 2.39/0.73    ! [X2,X1,X0] : (? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP1(sK11(X0,X1,X2),X1,X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sP1(sK11(X0,X1,X2),X1,X0) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 2.39/0.73    introduced(choice_axiom,[])).
% 2.39/0.73  fof(f51,plain,(
% 2.39/0.73    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 2.39/0.73    inference(rectify,[],[f50])).
% 2.39/0.73  fof(f50,plain,(
% 2.39/0.73    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X3,X1,X0)) & (sP1(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 2.39/0.73    inference(nnf_transformation,[],[f34])).
% 2.39/0.73  fof(f3313,plain,(
% 2.39/0.73    spl16_22 | ~spl16_23 | ~spl16_9 | ~spl16_15 | spl16_16 | ~spl16_39 | ~spl16_61),
% 2.39/0.73    inference(avatar_split_clause,[],[f3312,f2966,f910,f521,f517,f207,f694,f691])).
% 2.39/0.73  fof(f694,plain,(
% 2.39/0.73    spl16_23 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_23])])).
% 2.39/0.73  fof(f517,plain,(
% 2.39/0.73    spl16_15 <=> sP3(sK8,sK6,sK5,sK4)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_15])])).
% 2.39/0.73  fof(f521,plain,(
% 2.39/0.73    spl16_16 <=> sK7 = k2_mcart_1(sK8)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).
% 2.39/0.73  fof(f910,plain,(
% 2.39/0.73    spl16_39 <=> sK8 = k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).
% 2.39/0.73  fof(f2966,plain,(
% 2.39/0.73    spl16_61 <=> m1_subset_1(k2_mcart_1(sK8),sK6)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_61])])).
% 2.39/0.73  fof(f3312,plain,(
% 2.39/0.73    ( ! [X17,X16] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4) | ~sP1(k1_mcart_1(sK8),X16,X17)) ) | (~spl16_9 | ~spl16_15 | spl16_16 | ~spl16_39 | ~spl16_61)),
% 2.39/0.73    inference(subsumption_resolution,[],[f3311,f2968])).
% 2.39/0.73  fof(f2968,plain,(
% 2.39/0.73    m1_subset_1(k2_mcart_1(sK8),sK6) | ~spl16_61),
% 2.39/0.73    inference(avatar_component_clause,[],[f2966])).
% 2.39/0.73  fof(f3311,plain,(
% 2.39/0.73    ( ! [X17,X16] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4) | ~m1_subset_1(k2_mcart_1(sK8),sK6) | ~sP1(k1_mcart_1(sK8),X16,X17)) ) | (~spl16_9 | ~spl16_15 | spl16_16 | ~spl16_39)),
% 2.39/0.73    inference(subsumption_resolution,[],[f1252,f3253])).
% 2.39/0.73  fof(f3253,plain,(
% 2.39/0.73    m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK5) | ~spl16_15),
% 2.39/0.73    inference(subsumption_resolution,[],[f3235,f518])).
% 2.39/0.73  fof(f518,plain,(
% 2.39/0.73    sP3(sK8,sK6,sK5,sK4) | ~spl16_15),
% 2.39/0.73    inference(avatar_component_clause,[],[f517])).
% 2.39/0.73  fof(f3235,plain,(
% 2.39/0.73    m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK5) | ~sP3(sK8,sK6,sK5,sK4)),
% 2.39/0.73    inference(resolution,[],[f641,f116])).
% 2.39/0.73  fof(f116,plain,(
% 2.39/0.73    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.39/0.73    inference(definition_unfolding,[],[f67,f87])).
% 2.39/0.73  fof(f87,plain,(
% 2.39/0.73    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f9])).
% 2.39/0.73  fof(f9,axiom,(
% 2.39/0.73    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.39/0.73  fof(f67,plain,(
% 2.39/0.73    m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.39/0.73    inference(cnf_transformation,[],[f39])).
% 2.39/0.73  fof(f39,plain,(
% 2.39/0.73    sK7 != k7_mcart_1(sK4,sK5,sK6,sK8) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X5] : (! [X6] : (! [X7] : (sK7 = X7 | k3_mcart_1(X5,X6,X7) != sK8 | ~m1_subset_1(X7,sK6)) | ~m1_subset_1(X6,sK5)) | ~m1_subset_1(X5,sK4)) & m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.39/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f21,f38])).
% 2.39/0.73  fof(f38,plain,(
% 2.39/0.73    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK7 != k7_mcart_1(sK4,sK5,sK6,sK8) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X5] : (! [X6] : (! [X7] : (sK7 = X7 | k3_mcart_1(X5,X6,X7) != sK8 | ~m1_subset_1(X7,sK6)) | ~m1_subset_1(X6,sK5)) | ~m1_subset_1(X5,sK4)) & m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6)))),
% 2.39/0.73    introduced(choice_axiom,[])).
% 2.39/0.73  fof(f21,plain,(
% 2.39/0.73    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.39/0.73    inference(flattening,[],[f20])).
% 2.39/0.73  fof(f20,plain,(
% 2.39/0.73    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.39/0.73    inference(ennf_transformation,[],[f19])).
% 2.39/0.73  fof(f19,negated_conjecture,(
% 2.39/0.73    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.39/0.73    inference(negated_conjecture,[],[f18])).
% 2.39/0.73  fof(f18,conjecture,(
% 2.39/0.73    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 2.39/0.73  fof(f641,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1) | ~sP3(X3,X2,X1,X0)) )),
% 2.39/0.73    inference(superposition,[],[f122,f105])).
% 2.39/0.73  fof(f105,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) | ~sP3(X0,X1,X2,X3)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f62])).
% 2.39/0.73  fof(f62,plain,(
% 2.39/0.73    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP3(X0,X1,X2,X3))),
% 2.39/0.73    inference(rectify,[],[f61])).
% 2.39/0.73  fof(f61,plain,(
% 2.39/0.73    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP3(X3,X2,X1,X0))),
% 2.39/0.73    inference(nnf_transformation,[],[f36])).
% 2.39/0.73  fof(f36,plain,(
% 2.39/0.73    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP3(X3,X2,X1,X0))),
% 2.39/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.39/0.73  fof(f122,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.39/0.73    inference(definition_unfolding,[],[f109,f87])).
% 2.39/0.73  fof(f109,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.39/0.73    inference(cnf_transformation,[],[f28])).
% 2.39/0.73  fof(f28,plain,(
% 2.39/0.73    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.39/0.73    inference(ennf_transformation,[],[f11])).
% 2.39/0.73  fof(f11,axiom,(
% 2.39/0.73    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 2.39/0.73  fof(f1252,plain,(
% 2.39/0.73    ( ! [X17,X16] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK5) | ~m1_subset_1(k2_mcart_1(sK8),sK6) | ~sP1(k1_mcart_1(sK8),X16,X17)) ) | (~spl16_9 | spl16_16 | ~spl16_39)),
% 2.39/0.73    inference(forward_demodulation,[],[f1251,f668])).
% 2.39/0.73  fof(f668,plain,(
% 2.39/0.73    k1_mcart_1(k1_mcart_1(sK8)) = sK14(k1_mcart_1(sK8)) | ~spl16_9),
% 2.39/0.73    inference(resolution,[],[f227,f431])).
% 2.39/0.73  fof(f431,plain,(
% 2.39/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k1_mcart_1(X0) = sK14(X0)) )),
% 2.39/0.73    inference(superposition,[],[f80,f108])).
% 2.39/0.73  fof(f108,plain,(
% 2.39/0.73    ( ! [X2,X0,X1] : (k4_tarski(sK14(X0),sK15(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.39/0.73    inference(cnf_transformation,[],[f64])).
% 2.39/0.73  fof(f64,plain,(
% 2.39/0.73    ! [X0,X1,X2] : (k4_tarski(sK14(X0),sK15(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.39/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f27,f63])).
% 2.39/0.73  fof(f63,plain,(
% 2.39/0.73    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK14(X0),sK15(X0)) = X0)),
% 2.39/0.73    introduced(choice_axiom,[])).
% 2.39/0.73  fof(f27,plain,(
% 2.39/0.73    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.39/0.73    inference(ennf_transformation,[],[f3])).
% 2.39/0.73  fof(f3,axiom,(
% 2.39/0.73    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 2.39/0.73  fof(f80,plain,(
% 2.39/0.73    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.39/0.73    inference(cnf_transformation,[],[f16])).
% 2.39/0.73  fof(f16,axiom,(
% 2.39/0.73    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 2.39/0.73  fof(f1251,plain,(
% 2.39/0.73    ( ! [X17,X16] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK5) | ~m1_subset_1(k2_mcart_1(sK8),sK6) | ~m1_subset_1(sK14(k1_mcart_1(sK8)),sK4) | ~sP1(k1_mcart_1(sK8),X16,X17)) ) | (~spl16_9 | spl16_16 | ~spl16_39)),
% 2.39/0.73    inference(forward_demodulation,[],[f1250,f669])).
% 2.39/0.73  fof(f669,plain,(
% 2.39/0.73    k2_mcart_1(k1_mcart_1(sK8)) = sK15(k1_mcart_1(sK8)) | ~spl16_9),
% 2.39/0.73    inference(resolution,[],[f227,f432])).
% 2.39/0.73  fof(f432,plain,(
% 2.39/0.73    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_zfmisc_1(X4,X5)) | k2_mcart_1(X3) = sK15(X3)) )),
% 2.39/0.73    inference(superposition,[],[f81,f108])).
% 2.39/0.73  fof(f81,plain,(
% 2.39/0.73    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.39/0.73    inference(cnf_transformation,[],[f16])).
% 2.39/0.73  fof(f1250,plain,(
% 2.39/0.73    ( ! [X17,X16] : (~m1_subset_1(k2_mcart_1(sK8),sK6) | ~m1_subset_1(sK15(k1_mcart_1(sK8)),sK5) | ~m1_subset_1(sK14(k1_mcart_1(sK8)),sK4) | ~sP1(k1_mcart_1(sK8),X16,X17)) ) | (spl16_16 | ~spl16_39)),
% 2.39/0.73    inference(subsumption_resolution,[],[f1241,f523])).
% 2.39/0.73  fof(f523,plain,(
% 2.39/0.73    sK7 != k2_mcart_1(sK8) | spl16_16),
% 2.39/0.73    inference(avatar_component_clause,[],[f521])).
% 2.39/0.73  fof(f1241,plain,(
% 2.39/0.73    ( ! [X17,X16] : (~m1_subset_1(k2_mcart_1(sK8),sK6) | ~m1_subset_1(sK15(k1_mcart_1(sK8)),sK5) | ~m1_subset_1(sK14(k1_mcart_1(sK8)),sK4) | sK7 = k2_mcart_1(sK8) | ~sP1(k1_mcart_1(sK8),X16,X17)) ) | ~spl16_39),
% 2.39/0.73    inference(trivial_inequality_removal,[],[f1240])).
% 2.39/0.73  fof(f1240,plain,(
% 2.39/0.73    ( ! [X17,X16] : (sK8 != sK8 | ~m1_subset_1(k2_mcart_1(sK8),sK6) | ~m1_subset_1(sK15(k1_mcart_1(sK8)),sK5) | ~m1_subset_1(sK14(k1_mcart_1(sK8)),sK4) | sK7 = k2_mcart_1(sK8) | ~sP1(k1_mcart_1(sK8),X16,X17)) ) | ~spl16_39),
% 2.39/0.73    inference(superposition,[],[f571,f912])).
% 2.39/0.73  fof(f912,plain,(
% 2.39/0.73    sK8 = k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8)) | ~spl16_39),
% 2.39/0.73    inference(avatar_component_clause,[],[f910])).
% 2.39/0.73  fof(f571,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (sK8 != k4_tarski(X1,X0) | ~m1_subset_1(X0,sK6) | ~m1_subset_1(sK15(X1),sK5) | ~m1_subset_1(sK14(X1),sK4) | sK7 = X0 | ~sP1(X1,X2,X3)) )),
% 2.39/0.73    inference(resolution,[],[f435,f392])).
% 2.39/0.73  fof(f392,plain,(
% 2.39/0.73    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_zfmisc_1(X2,X1)) | ~sP1(X0,X1,X2)) )),
% 2.39/0.73    inference(resolution,[],[f91,f130])).
% 2.39/0.73  fof(f91,plain,(
% 2.39/0.73    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f53])).
% 2.39/0.73  fof(f435,plain,(
% 2.39/0.73    ( ! [X19,X17,X18,X16] : (~r2_hidden(X16,k2_zfmisc_1(X18,X19)) | sK7 = X17 | ~m1_subset_1(X17,sK6) | ~m1_subset_1(sK15(X16),sK5) | ~m1_subset_1(sK14(X16),sK4) | sK8 != k4_tarski(X16,X17)) )),
% 2.39/0.73    inference(superposition,[],[f115,f108])).
% 2.39/0.73  fof(f115,plain,(
% 2.39/0.73    ( ! [X6,X7,X5] : (sK8 != k4_tarski(k4_tarski(X5,X6),X7) | sK7 = X7 | ~m1_subset_1(X7,sK6) | ~m1_subset_1(X6,sK5) | ~m1_subset_1(X5,sK4)) )),
% 2.39/0.73    inference(definition_unfolding,[],[f68,f86])).
% 2.39/0.73  fof(f86,plain,(
% 2.39/0.73    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f8])).
% 2.39/0.73  fof(f8,axiom,(
% 2.39/0.73    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.39/0.73  fof(f68,plain,(
% 2.39/0.73    ( ! [X6,X7,X5] : (sK7 = X7 | k3_mcart_1(X5,X6,X7) != sK8 | ~m1_subset_1(X7,sK6) | ~m1_subset_1(X6,sK5) | ~m1_subset_1(X5,sK4)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f39])).
% 2.39/0.73  fof(f3284,plain,(
% 2.39/0.73    spl16_23 | ~spl16_15),
% 2.39/0.73    inference(avatar_split_clause,[],[f3283,f517,f694])).
% 2.39/0.73  fof(f3283,plain,(
% 2.39/0.73    m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4) | ~spl16_15),
% 2.39/0.73    inference(subsumption_resolution,[],[f3265,f518])).
% 2.39/0.73  fof(f3265,plain,(
% 2.39/0.73    m1_subset_1(k1_mcart_1(k1_mcart_1(sK8)),sK4) | ~sP3(sK8,sK6,sK5,sK4)),
% 2.39/0.73    inference(resolution,[],[f656,f116])).
% 2.39/0.73  fof(f656,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0) | ~sP3(X3,X2,X1,X0)) )),
% 2.39/0.73    inference(superposition,[],[f123,f104])).
% 2.39/0.73  fof(f104,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) | ~sP3(X0,X1,X2,X3)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f62])).
% 2.39/0.73  fof(f123,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.39/0.73    inference(definition_unfolding,[],[f110,f87])).
% 2.39/0.73  fof(f110,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.39/0.73    inference(cnf_transformation,[],[f29])).
% 2.39/0.73  fof(f29,plain,(
% 2.39/0.73    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.39/0.73    inference(ennf_transformation,[],[f10])).
% 2.39/0.73  fof(f10,axiom,(
% 2.39/0.73    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 2.39/0.73  fof(f3260,plain,(
% 2.39/0.73    spl16_34 | spl16_39 | ~spl16_9),
% 2.39/0.73    inference(avatar_split_clause,[],[f3259,f207,f910,f836])).
% 2.39/0.73  fof(f836,plain,(
% 2.39/0.73    spl16_34 <=> ! [X1,X0] : ~r2_hidden(sK8,k2_zfmisc_1(X0,X1))),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).
% 2.39/0.73  fof(f3259,plain,(
% 2.39/0.73    ( ! [X0,X1] : (sK8 = k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8)) | ~r2_hidden(sK8,k2_zfmisc_1(X0,X1))) ) | ~spl16_9),
% 2.39/0.73    inference(forward_demodulation,[],[f3258,f781])).
% 2.39/0.73  fof(f781,plain,(
% 2.39/0.73    k2_mcart_1(sK8) = sK15(sK8) | ~spl16_9),
% 2.39/0.73    inference(resolution,[],[f209,f432])).
% 2.39/0.73  fof(f3258,plain,(
% 2.39/0.73    ( ! [X0,X1] : (sK8 = k4_tarski(k1_mcart_1(sK8),sK15(sK8)) | ~r2_hidden(sK8,k2_zfmisc_1(X0,X1))) ) | ~spl16_9),
% 2.39/0.73    inference(superposition,[],[f108,f780])).
% 2.39/0.73  fof(f780,plain,(
% 2.39/0.73    k1_mcart_1(sK8) = sK14(sK8) | ~spl16_9),
% 2.39/0.73    inference(resolution,[],[f209,f431])).
% 2.39/0.73  fof(f2974,plain,(
% 2.39/0.73    spl16_61 | ~spl16_15),
% 2.39/0.73    inference(avatar_split_clause,[],[f2961,f517,f2966])).
% 2.39/0.73  fof(f2961,plain,(
% 2.39/0.73    m1_subset_1(k2_mcart_1(sK8),sK6) | ~spl16_15),
% 2.39/0.73    inference(subsumption_resolution,[],[f2943,f518])).
% 2.39/0.73  fof(f2943,plain,(
% 2.39/0.73    m1_subset_1(k2_mcart_1(sK8),sK6) | ~sP3(sK8,sK6,sK5,sK4)),
% 2.39/0.73    inference(resolution,[],[f734,f116])).
% 2.39/0.73  fof(f734,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k2_mcart_1(X3),X2) | ~sP3(X3,X2,X1,X0)) )),
% 2.39/0.73    inference(superposition,[],[f124,f106])).
% 2.39/0.73  fof(f106,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) | ~sP3(X0,X1,X2,X3)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f62])).
% 2.39/0.73  fof(f124,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.39/0.73    inference(definition_unfolding,[],[f111,f87])).
% 2.39/0.73  fof(f111,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.39/0.73    inference(cnf_transformation,[],[f30])).
% 2.39/0.73  fof(f30,plain,(
% 2.39/0.73    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.39/0.73    inference(ennf_transformation,[],[f12])).
% 2.39/0.73  fof(f12,axiom,(
% 2.39/0.73    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 2.39/0.73  fof(f1001,plain,(
% 2.39/0.73    ~spl16_38),
% 2.39/0.73    inference(avatar_contradiction_clause,[],[f1000])).
% 2.39/0.73  fof(f1000,plain,(
% 2.39/0.73    $false | ~spl16_38),
% 2.39/0.73    inference(subsumption_resolution,[],[f995,f70])).
% 2.39/0.73  fof(f70,plain,(
% 2.39/0.73    k1_xboole_0 != sK5),
% 2.39/0.73    inference(cnf_transformation,[],[f39])).
% 2.39/0.73  fof(f995,plain,(
% 2.39/0.73    k1_xboole_0 = sK5 | ~spl16_38),
% 2.39/0.73    inference(resolution,[],[f873,f77])).
% 2.39/0.73  fof(f77,plain,(
% 2.39/0.73    ( ! [X0] : (r2_hidden(sK10(X0),X0) | k1_xboole_0 = X0) )),
% 2.39/0.73    inference(cnf_transformation,[],[f47])).
% 2.39/0.73  fof(f47,plain,(
% 2.39/0.73    ! [X0] : ((sP0(sK10(X0),X0) & r2_hidden(sK10(X0),X0)) | k1_xboole_0 = X0)),
% 2.39/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f32,f46])).
% 2.39/0.73  fof(f46,plain,(
% 2.39/0.73    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK10(X0),X0) & r2_hidden(sK10(X0),X0)))),
% 2.39/0.73    introduced(choice_axiom,[])).
% 2.39/0.73  fof(f32,plain,(
% 2.39/0.73    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.39/0.73    inference(definition_folding,[],[f22,f31])).
% 2.39/0.73  fof(f31,plain,(
% 2.39/0.73    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 2.39/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.39/0.73  fof(f22,plain,(
% 2.39/0.73    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.39/0.73    inference(ennf_transformation,[],[f17])).
% 2.39/0.73  fof(f17,axiom,(
% 2.39/0.73    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 2.39/0.73  fof(f873,plain,(
% 2.39/0.73    ( ! [X1] : (~r2_hidden(X1,sK5)) ) | ~spl16_38),
% 2.39/0.73    inference(avatar_component_clause,[],[f872])).
% 2.39/0.73  fof(f872,plain,(
% 2.39/0.73    spl16_38 <=> ! [X1] : ~r2_hidden(X1,sK5)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).
% 2.39/0.73  fof(f993,plain,(
% 2.39/0.73    ~spl16_37),
% 2.39/0.73    inference(avatar_contradiction_clause,[],[f992])).
% 2.39/0.73  fof(f992,plain,(
% 2.39/0.73    $false | ~spl16_37),
% 2.39/0.73    inference(subsumption_resolution,[],[f987,f69])).
% 2.39/0.73  fof(f69,plain,(
% 2.39/0.73    k1_xboole_0 != sK4),
% 2.39/0.73    inference(cnf_transformation,[],[f39])).
% 2.39/0.73  fof(f987,plain,(
% 2.39/0.73    k1_xboole_0 = sK4 | ~spl16_37),
% 2.39/0.73    inference(resolution,[],[f870,f77])).
% 2.39/0.73  fof(f870,plain,(
% 2.39/0.73    ( ! [X2] : (~r2_hidden(X2,sK4)) ) | ~spl16_37),
% 2.39/0.73    inference(avatar_component_clause,[],[f869])).
% 2.39/0.73  fof(f869,plain,(
% 2.39/0.73    spl16_37 <=> ! [X2] : ~r2_hidden(X2,sK4)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_37])])).
% 2.39/0.73  fof(f983,plain,(
% 2.39/0.73    spl16_32 | ~spl16_34),
% 2.39/0.73    inference(avatar_split_clause,[],[f927,f836,f806])).
% 2.39/0.73  fof(f806,plain,(
% 2.39/0.73    spl16_32 <=> ! [X1,X0] : ~sP1(sK8,X0,X1)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_32])])).
% 2.39/0.73  fof(f927,plain,(
% 2.39/0.73    ( ! [X0,X1] : (~sP1(sK8,X0,X1)) ) | ~spl16_34),
% 2.39/0.73    inference(resolution,[],[f837,f392])).
% 2.39/0.73  fof(f837,plain,(
% 2.39/0.73    ( ! [X0,X1] : (~r2_hidden(sK8,k2_zfmisc_1(X0,X1))) ) | ~spl16_34),
% 2.39/0.73    inference(avatar_component_clause,[],[f836])).
% 2.39/0.73  fof(f982,plain,(
% 2.39/0.73    ~spl16_9 | ~spl16_32),
% 2.39/0.73    inference(avatar_contradiction_clause,[],[f981])).
% 2.39/0.73  fof(f981,plain,(
% 2.39/0.73    $false | (~spl16_9 | ~spl16_32)),
% 2.39/0.73    inference(subsumption_resolution,[],[f397,f807])).
% 2.39/0.73  fof(f807,plain,(
% 2.39/0.73    ( ! [X0,X1] : (~sP1(sK8,X0,X1)) ) | ~spl16_32),
% 2.39/0.73    inference(avatar_component_clause,[],[f806])).
% 2.39/0.73  fof(f397,plain,(
% 2.39/0.73    sP1(sK8,sK6,k2_zfmisc_1(sK4,sK5)) | ~spl16_9),
% 2.39/0.73    inference(resolution,[],[f387,f209])).
% 2.39/0.73  fof(f958,plain,(
% 2.39/0.73    spl16_15),
% 2.39/0.73    inference(avatar_split_clause,[],[f957,f517])).
% 2.39/0.73  fof(f957,plain,(
% 2.39/0.73    sP3(sK8,sK6,sK5,sK4)),
% 2.39/0.73    inference(subsumption_resolution,[],[f956,f69])).
% 2.39/0.73  fof(f956,plain,(
% 2.39/0.73    sP3(sK8,sK6,sK5,sK4) | k1_xboole_0 = sK4),
% 2.39/0.73    inference(subsumption_resolution,[],[f955,f70])).
% 2.39/0.73  fof(f955,plain,(
% 2.39/0.73    sP3(sK8,sK6,sK5,sK4) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 2.39/0.73    inference(subsumption_resolution,[],[f935,f71])).
% 2.39/0.73  fof(f71,plain,(
% 2.39/0.73    k1_xboole_0 != sK6),
% 2.39/0.73    inference(cnf_transformation,[],[f39])).
% 2.39/0.73  fof(f935,plain,(
% 2.39/0.73    sP3(sK8,sK6,sK5,sK4) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 2.39/0.73    inference(resolution,[],[f121,f116])).
% 2.39/0.73  fof(f121,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP3(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.39/0.73    inference(definition_unfolding,[],[f107,f87])).
% 2.39/0.73  fof(f107,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (sP3(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.39/0.73    inference(cnf_transformation,[],[f37])).
% 2.39/0.73  fof(f37,plain,(
% 2.39/0.73    ! [X0,X1,X2] : (! [X3] : (sP3(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.39/0.73    inference(definition_folding,[],[f26,f36])).
% 2.39/0.73  fof(f26,plain,(
% 2.39/0.73    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.39/0.73    inference(ennf_transformation,[],[f15])).
% 2.39/0.73  fof(f15,axiom,(
% 2.39/0.73    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.39/0.73  fof(f874,plain,(
% 2.39/0.73    spl16_37 | spl16_38 | ~spl16_18),
% 2.39/0.73    inference(avatar_split_clause,[],[f860,f625,f872,f869])).
% 2.39/0.73  fof(f625,plain,(
% 2.39/0.73    spl16_18 <=> ! [X0] : ~r2_hidden(X0,k2_zfmisc_1(sK4,sK5))),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_18])])).
% 2.39/0.73  fof(f860,plain,(
% 2.39/0.73    ( ! [X2,X1] : (~r2_hidden(X1,sK5) | ~r2_hidden(X2,sK4)) ) | ~spl16_18),
% 2.39/0.73    inference(resolution,[],[f626,f114])).
% 2.39/0.73  fof(f114,plain,(
% 2.39/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.39/0.73    inference(cnf_transformation,[],[f66])).
% 2.39/0.73  fof(f66,plain,(
% 2.39/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.39/0.73    inference(flattening,[],[f65])).
% 2.39/0.73  fof(f65,plain,(
% 2.39/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.39/0.73    inference(nnf_transformation,[],[f4])).
% 2.39/0.73  fof(f4,axiom,(
% 2.39/0.73    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.39/0.73  fof(f626,plain,(
% 2.39/0.73    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK4,sK5))) ) | ~spl16_18),
% 2.39/0.73    inference(avatar_component_clause,[],[f625])).
% 2.39/0.73  fof(f855,plain,(
% 2.39/0.73    ~spl16_17),
% 2.39/0.73    inference(avatar_contradiction_clause,[],[f854])).
% 2.39/0.73  fof(f854,plain,(
% 2.39/0.73    $false | ~spl16_17),
% 2.39/0.73    inference(subsumption_resolution,[],[f849,f71])).
% 2.39/0.73  fof(f849,plain,(
% 2.39/0.73    k1_xboole_0 = sK6 | ~spl16_17),
% 2.39/0.73    inference(resolution,[],[f623,f77])).
% 2.39/0.73  fof(f623,plain,(
% 2.39/0.73    ( ! [X1] : (~r2_hidden(X1,sK6)) ) | ~spl16_17),
% 2.39/0.73    inference(avatar_component_clause,[],[f622])).
% 2.39/0.73  fof(f622,plain,(
% 2.39/0.73    spl16_17 <=> ! [X1] : ~r2_hidden(X1,sK6)),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_17])])).
% 2.39/0.73  fof(f627,plain,(
% 2.39/0.73    spl16_17 | spl16_18 | ~spl16_10),
% 2.39/0.73    inference(avatar_split_clause,[],[f609,f211,f625,f622])).
% 2.39/0.73  fof(f211,plain,(
% 2.39/0.73    spl16_10 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.39/0.73    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).
% 2.39/0.73  fof(f609,plain,(
% 2.39/0.73    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) | ~r2_hidden(X1,sK6)) ) | ~spl16_10),
% 2.39/0.73    inference(resolution,[],[f544,f213])).
% 2.39/0.73  fof(f213,plain,(
% 2.39/0.73    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl16_10),
% 2.39/0.73    inference(avatar_component_clause,[],[f211])).
% 2.39/0.73  fof(f544,plain,(
% 2.39/0.73    ( ! [X30,X28,X29,X27] : (~v1_xboole_0(k2_zfmisc_1(X30,X28)) | ~r2_hidden(X29,X30) | ~r2_hidden(X27,X28)) )),
% 2.39/0.73    inference(resolution,[],[f114,f73])).
% 2.39/0.74  fof(f73,plain,(
% 2.39/0.74    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.39/0.74    inference(cnf_transformation,[],[f43])).
% 2.39/0.74  fof(f43,plain,(
% 2.39/0.74    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK9(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.39/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).
% 2.39/0.74  fof(f42,plain,(
% 2.39/0.74    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 2.39/0.74    introduced(choice_axiom,[])).
% 2.39/0.74  fof(f41,plain,(
% 2.39/0.74    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.39/0.74    inference(rectify,[],[f40])).
% 2.39/0.74  fof(f40,plain,(
% 2.39/0.74    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.39/0.74    inference(nnf_transformation,[],[f1])).
% 2.39/0.74  fof(f1,axiom,(
% 2.39/0.74    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.39/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.39/0.74  fof(f524,plain,(
% 2.39/0.74    ~spl16_15 | ~spl16_16),
% 2.39/0.74    inference(avatar_split_clause,[],[f515,f521,f517])).
% 2.39/0.74  fof(f515,plain,(
% 2.39/0.74    sK7 != k2_mcart_1(sK8) | ~sP3(sK8,sK6,sK5,sK4)),
% 2.39/0.74    inference(superposition,[],[f72,f106])).
% 2.39/0.74  fof(f72,plain,(
% 2.39/0.74    sK7 != k7_mcart_1(sK4,sK5,sK6,sK8)),
% 2.39/0.74    inference(cnf_transformation,[],[f39])).
% 2.39/0.74  fof(f214,plain,(
% 2.39/0.74    spl16_9 | spl16_10),
% 2.39/0.74    inference(avatar_split_clause,[],[f205,f211,f207])).
% 2.39/0.74  fof(f205,plain,(
% 2.39/0.74    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.39/0.74    inference(resolution,[],[f82,f116])).
% 2.39/0.74  fof(f82,plain,(
% 2.39/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.39/0.74    inference(cnf_transformation,[],[f24])).
% 2.39/0.74  fof(f24,plain,(
% 2.39/0.74    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.39/0.74    inference(flattening,[],[f23])).
% 2.39/0.74  fof(f23,plain,(
% 2.39/0.74    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.39/0.74    inference(ennf_transformation,[],[f7])).
% 2.39/0.74  fof(f7,axiom,(
% 2.39/0.74    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.39/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.39/0.74  % SZS output end Proof for theBenchmark
% 2.39/0.74  % (15710)------------------------------
% 2.39/0.74  % (15710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.74  % (15710)Termination reason: Refutation
% 2.39/0.74  
% 2.39/0.74  % (15710)Memory used [KB]: 7547
% 2.39/0.74  % (15710)Time elapsed: 0.306 s
% 2.39/0.74  % (15710)------------------------------
% 2.39/0.74  % (15710)------------------------------
% 2.39/0.74  % (15682)Success in time 0.379 s
%------------------------------------------------------------------------------
