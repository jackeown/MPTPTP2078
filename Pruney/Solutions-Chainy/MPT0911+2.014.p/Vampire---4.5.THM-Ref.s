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

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 427 expanded)
%              Number of leaves         :   38 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          :  611 (1993 expanded)
%              Number of equality atoms :  175 ( 853 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f292,f327,f382,f415,f609,f611,f644,f669,f1869,f2065,f2092,f2109,f2125])).

fof(f2125,plain,
    ( ~ spl15_1
    | ~ spl15_22 ),
    inference(avatar_contradiction_clause,[],[f2124])).

fof(f2124,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_22 ),
    inference(subsumption_resolution,[],[f428,f455])).

fof(f455,plain,
    ( ! [X0,X1] : ~ sP0(k1_mcart_1(sK7),X0,X1)
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl15_22
  <=> ! [X1,X0] : ~ sP0(k1_mcart_1(sK7),X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f428,plain,
    ( sP0(k1_mcart_1(sK7),sK4,sK3)
    | ~ spl15_1 ),
    inference(resolution,[],[f357,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f82,f117])).

fof(f117,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f31,f30])).

fof(f30,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK10(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP0(sK10(X0,X1,X2),X1,X0)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK10(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP0(sK10(X0,X1,X2),X1,X0)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f357,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4))
    | ~ spl15_1 ),
    inference(resolution,[],[f133,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f133,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl15_1
  <=> r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f2109,plain,
    ( spl15_22
    | ~ spl15_23
    | ~ spl15_12
    | spl15_13
    | ~ spl15_18
    | ~ spl15_43 ),
    inference(avatar_split_clause,[],[f2108,f1861,f406,f379,f375,f457,f454])).

fof(f457,plain,
    ( spl15_23
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).

fof(f375,plain,
    ( spl15_12
  <=> sP2(sK7,sK5,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f379,plain,
    ( spl15_13
  <=> sK6 = k2_mcart_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f406,plain,
    ( spl15_18
  <=> sK7 = k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f1861,plain,
    ( spl15_43
  <=> m1_subset_1(k2_mcart_1(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).

fof(f2108,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ sP0(k1_mcart_1(sK7),X5,X6) )
    | ~ spl15_12
    | spl15_13
    | ~ spl15_18
    | ~ spl15_43 ),
    inference(subsumption_resolution,[],[f2107,f2058])).

fof(f2058,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f2040,f376])).

fof(f376,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f375])).

fof(f2040,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(resolution,[],[f462,f105])).

fof(f105,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f61,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK6 != k7_mcart_1(sK3,sK4,sK5,sK7)
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X7
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f35])).

fof(f35,plain,
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
   => ( sK6 != k7_mcart_1(sK3,sK4,sK5,sK7)
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X7
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f462,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1)
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f111,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f101,f79])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f2107,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4)
        | ~ sP0(k1_mcart_1(sK7),X5,X6) )
    | spl15_13
    | ~ spl15_18
    | ~ spl15_43 ),
    inference(subsumption_resolution,[],[f2106,f1863])).

fof(f1863,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5)
    | ~ spl15_43 ),
    inference(avatar_component_clause,[],[f1861])).

fof(f2106,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4)
        | ~ sP0(k1_mcart_1(sK7),X5,X6) )
    | spl15_13
    | ~ spl15_18 ),
    inference(subsumption_resolution,[],[f1034,f381])).

fof(f381,plain,
    ( sK6 != k2_mcart_1(sK7)
    | spl15_13 ),
    inference(avatar_component_clause,[],[f379])).

fof(f1034,plain,
    ( ! [X6,X5] :
        ( sK6 = k2_mcart_1(sK7)
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4)
        | ~ sP0(k1_mcart_1(sK7),X5,X6) )
    | ~ spl15_18 ),
    inference(trivial_inequality_removal,[],[f1031])).

fof(f1031,plain,
    ( ! [X6,X5] :
        ( sK7 != sK7
        | sK6 = k2_mcart_1(sK7)
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4)
        | ~ sP0(k1_mcart_1(sK7),X5,X6) )
    | ~ spl15_18 ),
    inference(superposition,[],[f1029,f408])).

fof(f408,plain,
    ( sK7 = k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7))
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f406])).

fof(f1029,plain,(
    ! [X2,X0,X3,X1] :
      ( sK7 != k4_tarski(X0,X3)
      | sK6 = X3
      | ~ m1_subset_1(X3,sK5)
      | ~ m1_subset_1(k1_mcart_1(X0),sK3)
      | ~ m1_subset_1(k2_mcart_1(X0),sK4)
      | ~ sP0(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f1028])).

fof(f1028,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k1_mcart_1(X0),sK3)
      | sK6 = X3
      | ~ m1_subset_1(X3,sK5)
      | sK7 != k4_tarski(X0,X3)
      | ~ m1_subset_1(k2_mcart_1(X0),sK4)
      | ~ sP0(X0,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(superposition,[],[f942,f542])).

fof(f542,plain,(
    ! [X23,X21,X22] :
      ( sK11(X21,X22,X23) = k1_mcart_1(X21)
      | ~ sP0(X21,X22,X23) ) ),
    inference(superposition,[],[f70,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0
          & r2_hidden(sK12(X0,X1,X2),X1)
          & r2_hidden(sK11(X0,X1,X2),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0
        & r2_hidden(sK12(X0,X1,X2),X1)
        & r2_hidden(sK11(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f942,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK11(X0,X1,X2),sK3)
      | sK6 = X3
      | ~ m1_subset_1(X3,sK5)
      | sK7 != k4_tarski(X0,X3)
      | ~ m1_subset_1(k2_mcart_1(X0),sK4)
      | ~ sP0(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f937])).

fof(f937,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK4)
      | sK6 = X3
      | ~ m1_subset_1(X3,sK5)
      | sK7 != k4_tarski(X0,X3)
      | ~ m1_subset_1(sK11(X0,X1,X2),sK3)
      | ~ sP0(X0,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(superposition,[],[f540,f541])).

fof(f541,plain,(
    ! [X19,X20,X18] :
      ( sK12(X18,X19,X20) = k2_mcart_1(X18)
      | ~ sP0(X18,X19,X20) ) ),
    inference(superposition,[],[f71,f88])).

fof(f71,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f540,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ m1_subset_1(sK12(X14,X15,X16),sK4)
      | sK6 = X17
      | ~ m1_subset_1(X17,sK5)
      | sK7 != k4_tarski(X14,X17)
      | ~ m1_subset_1(sK11(X14,X15,X16),sK3)
      | ~ sP0(X14,X15,X16) ) ),
    inference(superposition,[],[f104,f88])).

fof(f104,plain,(
    ! [X6,X7,X5] :
      ( sK7 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK6 = X7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f62,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2092,plain,
    ( spl15_23
    | ~ spl15_12 ),
    inference(avatar_split_clause,[],[f2091,f375,f457])).

fof(f2091,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f2073,f376])).

fof(f2073,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(resolution,[],[f503,f105])).

fof(f503,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0)
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f112,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f102,f79])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f2065,plain,
    ( spl15_16
    | spl15_18
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f2064,f131,f406,f396])).

fof(f396,plain,
    ( spl15_16
  <=> ! [X1,X0] : ~ r2_hidden(sK7,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f2064,plain,
    ( ! [X0,X1] :
        ( sK7 = k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7))
        | ~ r2_hidden(sK7,k2_zfmisc_1(X0,X1)) )
    | ~ spl15_1 ),
    inference(forward_demodulation,[],[f2063,f353])).

fof(f353,plain,
    ( sK14(sK7) = k2_mcart_1(sK7)
    | ~ spl15_1 ),
    inference(resolution,[],[f133,f227])).

fof(f227,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k2_zfmisc_1(X5,X6))
      | sK14(X4) = k2_mcart_1(X4) ) ),
    inference(superposition,[],[f71,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK13(X0),sK14(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK13(X0),sK14(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f26,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK13(X0),sK14(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f2063,plain,
    ( ! [X0,X1] :
        ( sK7 = k4_tarski(k1_mcart_1(sK7),sK14(sK7))
        | ~ r2_hidden(sK7,k2_zfmisc_1(X0,X1)) )
    | ~ spl15_1 ),
    inference(superposition,[],[f100,f352])).

fof(f352,plain,
    ( k1_mcart_1(sK7) = sK13(sK7)
    | ~ spl15_1 ),
    inference(resolution,[],[f133,f228])).

fof(f228,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k2_zfmisc_1(X8,X9))
      | k1_mcart_1(X7) = sK13(X7) ) ),
    inference(superposition,[],[f70,f100])).

fof(f1869,plain,
    ( spl15_43
    | ~ spl15_12 ),
    inference(avatar_split_clause,[],[f1856,f375,f1861])).

fof(f1856,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5)
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f1838,f376])).

fof(f1838,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(resolution,[],[f515,f105])).

fof(f515,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k2_mcart_1(X3),X2)
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f113,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f103,f79])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f669,plain,(
    spl15_12 ),
    inference(avatar_split_clause,[],[f668,f375])).

fof(f668,plain,(
    sP2(sK7,sK5,sK4,sK3) ),
    inference(subsumption_resolution,[],[f667,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

fof(f667,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f666,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f666,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f650,f65])).

fof(f65,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f36])).

fof(f650,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f110,f105])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP2(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f99,f79])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP2(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f25,f33])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f644,plain,(
    ~ spl15_8 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | ~ spl15_8 ),
    inference(subsumption_resolution,[],[f640,f64])).

fof(f640,plain,
    ( k1_xboole_0 = sK4
    | ~ spl15_8 ),
    inference(resolution,[],[f614,f121])).

fof(f121,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f69,f114])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f614,plain,
    ( ! [X1] :
        ( r2_hidden(sK9(X1,sK4),X1)
        | sK4 = X1 )
    | ~ spl15_8 ),
    inference(resolution,[],[f344,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f344,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl15_8
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f611,plain,
    ( spl15_7
    | spl15_8
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f505,f290,f343,f340])).

fof(f340,plain,
    ( spl15_7
  <=> ! [X1] : ~ r2_hidden(X1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f290,plain,
    ( spl15_6
  <=> ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f505,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK4)
        | ~ r2_hidden(X1,sK3) )
    | ~ spl15_6 ),
    inference(resolution,[],[f328,f116])).

fof(f116,plain,(
    ! [X4,X2,X3,X1] :
      ( sP0(k4_tarski(X3,X4),X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f328,plain,
    ( ! [X0] : ~ sP0(X0,sK4,sK3)
    | ~ spl15_6 ),
    inference(resolution,[],[f291,f206])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f83,f117])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f291,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK3,sK4))
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f290])).

fof(f609,plain,(
    ~ spl15_7 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl15_7 ),
    inference(subsumption_resolution,[],[f605,f63])).

fof(f605,plain,
    ( k1_xboole_0 = sK3
    | ~ spl15_7 ),
    inference(resolution,[],[f499,f121])).

fof(f499,plain,
    ( ! [X1] :
        ( r2_hidden(sK9(X1,sK3),X1)
        | sK3 = X1 )
    | ~ spl15_7 ),
    inference(resolution,[],[f341,f73])).

fof(f341,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK3)
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f340])).

fof(f415,plain,
    ( ~ spl15_1
    | ~ spl15_16 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f133,f397])).

fof(f397,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK7,k2_zfmisc_1(X0,X1))
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f396])).

fof(f382,plain,
    ( ~ spl15_12
    | ~ spl15_13 ),
    inference(avatar_split_clause,[],[f373,f379,f375])).

fof(f373,plain,
    ( sK6 != k2_mcart_1(sK7)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(superposition,[],[f66,f98])).

fof(f66,plain,(
    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f327,plain,(
    ~ spl15_5 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f324,f65])).

fof(f324,plain,
    ( k1_xboole_0 = sK5
    | ~ spl15_5 ),
    inference(resolution,[],[f305,f121])).

fof(f305,plain,
    ( ! [X22] :
        ( r2_hidden(sK9(X22,sK5),X22)
        | sK5 = X22 )
    | ~ spl15_5 ),
    inference(resolution,[],[f73,f288])).

fof(f288,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK5)
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl15_5
  <=> ! [X1] : ~ r2_hidden(X1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f292,plain,
    ( spl15_5
    | spl15_6
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f278,f135,f290,f287])).

fof(f135,plain,
    ( spl15_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f278,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(sK3,sK4))
        | ~ r2_hidden(X1,sK5) )
    | ~ spl15_2 ),
    inference(resolution,[],[f254,f137])).

fof(f137,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f254,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X6,X4))
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f116,f213])).

fof(f213,plain,(
    ! [X12,X13,X11] :
      ( ~ sP0(X11,X12,X13)
      | ~ v1_xboole_0(k2_zfmisc_1(X13,X12)) ) ),
    inference(resolution,[],[f206,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f138,plain,
    ( spl15_1
    | spl15_2 ),
    inference(avatar_split_clause,[],[f129,f135,f131])).

fof(f129,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(resolution,[],[f72,f105])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (11981)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.48  % (11989)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (11976)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (11975)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (11977)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (11978)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11986)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (11987)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (11974)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (11996)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (11988)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (12002)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (11997)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (11980)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (11994)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (11984)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (11995)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (11976)Refutation not found, incomplete strategy% (11976)------------------------------
% 0.20/0.53  % (11976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11976)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11976)Memory used [KB]: 10746
% 0.20/0.53  % (11976)Time elapsed: 0.109 s
% 0.20/0.53  % (11976)------------------------------
% 0.20/0.53  % (11976)------------------------------
% 0.20/0.53  % (11998)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (11979)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (12000)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (11992)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (11990)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (11999)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (11991)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (11983)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (11993)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (11985)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (12001)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (11996)Refutation not found, incomplete strategy% (11996)------------------------------
% 0.20/0.54  % (11996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11996)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11996)Memory used [KB]: 11129
% 0.20/0.54  % (11996)Time elapsed: 0.090 s
% 0.20/0.54  % (11996)------------------------------
% 0.20/0.54  % (11996)------------------------------
% 0.20/0.54  % (11982)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (11982)Refutation not found, incomplete strategy% (11982)------------------------------
% 0.20/0.55  % (11982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12003)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (11995)Refutation not found, incomplete strategy% (11995)------------------------------
% 0.20/0.55  % (11995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11995)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11995)Memory used [KB]: 1791
% 0.20/0.55  % (11995)Time elapsed: 0.135 s
% 0.20/0.55  % (11995)------------------------------
% 0.20/0.55  % (11995)------------------------------
% 0.20/0.56  % (11994)Refutation not found, incomplete strategy% (11994)------------------------------
% 0.20/0.56  % (11994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (11982)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (11982)Memory used [KB]: 10746
% 1.50/0.56  % (11982)Time elapsed: 0.142 s
% 1.50/0.56  % (11982)------------------------------
% 1.50/0.56  % (11982)------------------------------
% 1.50/0.56  % (11994)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (11994)Memory used [KB]: 10874
% 1.50/0.56  % (11994)Time elapsed: 0.139 s
% 1.50/0.56  % (11994)------------------------------
% 1.50/0.56  % (11994)------------------------------
% 2.17/0.66  % (12007)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.17/0.68  % (12005)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.17/0.69  % (12006)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.17/0.69  % (12001)Refutation found. Thanks to Tanya!
% 2.17/0.69  % SZS status Theorem for theBenchmark
% 2.17/0.69  % SZS output start Proof for theBenchmark
% 2.17/0.69  fof(f2126,plain,(
% 2.17/0.69    $false),
% 2.17/0.69    inference(avatar_sat_refutation,[],[f138,f292,f327,f382,f415,f609,f611,f644,f669,f1869,f2065,f2092,f2109,f2125])).
% 2.17/0.69  fof(f2125,plain,(
% 2.17/0.69    ~spl15_1 | ~spl15_22),
% 2.17/0.69    inference(avatar_contradiction_clause,[],[f2124])).
% 2.17/0.69  fof(f2124,plain,(
% 2.17/0.69    $false | (~spl15_1 | ~spl15_22)),
% 2.17/0.69    inference(subsumption_resolution,[],[f428,f455])).
% 2.17/0.69  fof(f455,plain,(
% 2.17/0.69    ( ! [X0,X1] : (~sP0(k1_mcart_1(sK7),X0,X1)) ) | ~spl15_22),
% 2.17/0.69    inference(avatar_component_clause,[],[f454])).
% 2.17/0.69  fof(f454,plain,(
% 2.17/0.69    spl15_22 <=> ! [X1,X0] : ~sP0(k1_mcart_1(sK7),X0,X1)),
% 2.17/0.69    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).
% 2.17/0.69  fof(f428,plain,(
% 2.17/0.69    sP0(k1_mcart_1(sK7),sK4,sK3) | ~spl15_1),
% 2.17/0.69    inference(resolution,[],[f357,f197])).
% 2.17/0.69  fof(f197,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sP0(X0,X2,X1)) )),
% 2.17/0.69    inference(resolution,[],[f82,f117])).
% 2.17/0.69  fof(f117,plain,(
% 2.17/0.69    ( ! [X0,X1] : (sP1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 2.17/0.69    inference(equality_resolution,[],[f90])).
% 2.17/0.69  fof(f90,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.17/0.69    inference(cnf_transformation,[],[f54])).
% 2.17/0.69  fof(f54,plain,(
% 2.17/0.69    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 2.17/0.69    inference(nnf_transformation,[],[f32])).
% 2.17/0.69  fof(f32,plain,(
% 2.17/0.69    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 2.17/0.69    inference(definition_folding,[],[f3,f31,f30])).
% 2.17/0.69  fof(f30,plain,(
% 2.17/0.69    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 2.17/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.17/0.69  fof(f31,plain,(
% 2.17/0.69    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 2.17/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.17/0.69  fof(f3,axiom,(
% 2.17/0.69    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.17/0.69  fof(f82,plain,(
% 2.17/0.69    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X4,X1,X0)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f49])).
% 2.17/0.69  fof(f49,plain,(
% 2.17/0.69    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK10(X0,X1,X2),X1,X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP0(sK10(X0,X1,X2),X1,X0) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.17/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f47,f48])).
% 2.17/0.69  fof(f48,plain,(
% 2.17/0.69    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK10(X0,X1,X2),X1,X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP0(sK10(X0,X1,X2),X1,X0) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 2.17/0.69    introduced(choice_axiom,[])).
% 2.17/0.69  fof(f47,plain,(
% 2.17/0.69    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.17/0.69    inference(rectify,[],[f46])).
% 2.17/0.69  fof(f46,plain,(
% 2.17/0.69    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 2.17/0.69    inference(nnf_transformation,[],[f31])).
% 2.17/0.69  fof(f357,plain,(
% 2.17/0.69    r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) | ~spl15_1),
% 2.17/0.69    inference(resolution,[],[f133,f80])).
% 2.17/0.69  fof(f80,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f24])).
% 2.17/0.69  fof(f24,plain,(
% 2.17/0.69    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.17/0.69    inference(ennf_transformation,[],[f13])).
% 2.17/0.69  fof(f13,axiom,(
% 2.17/0.69    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.17/0.69  fof(f133,plain,(
% 2.17/0.69    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl15_1),
% 2.17/0.69    inference(avatar_component_clause,[],[f131])).
% 2.17/0.69  fof(f131,plain,(
% 2.17/0.69    spl15_1 <=> r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.17/0.69    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 2.17/0.69  fof(f2109,plain,(
% 2.17/0.69    spl15_22 | ~spl15_23 | ~spl15_12 | spl15_13 | ~spl15_18 | ~spl15_43),
% 2.17/0.69    inference(avatar_split_clause,[],[f2108,f1861,f406,f379,f375,f457,f454])).
% 2.17/0.69  fof(f457,plain,(
% 2.17/0.69    spl15_23 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)),
% 2.17/0.69    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).
% 2.17/0.69  fof(f375,plain,(
% 2.17/0.69    spl15_12 <=> sP2(sK7,sK5,sK4,sK3)),
% 2.17/0.69    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).
% 2.17/0.69  fof(f379,plain,(
% 2.17/0.69    spl15_13 <=> sK6 = k2_mcart_1(sK7)),
% 2.17/0.69    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).
% 2.17/0.69  fof(f406,plain,(
% 2.17/0.69    spl15_18 <=> sK7 = k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7))),
% 2.17/0.69    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).
% 2.17/0.69  fof(f1861,plain,(
% 2.17/0.69    spl15_43 <=> m1_subset_1(k2_mcart_1(sK7),sK5)),
% 2.17/0.69    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).
% 2.17/0.69  fof(f2108,plain,(
% 2.17/0.69    ( ! [X6,X5] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~sP0(k1_mcart_1(sK7),X5,X6)) ) | (~spl15_12 | spl15_13 | ~spl15_18 | ~spl15_43)),
% 2.17/0.69    inference(subsumption_resolution,[],[f2107,f2058])).
% 2.17/0.69  fof(f2058,plain,(
% 2.17/0.69    m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) | ~spl15_12),
% 2.17/0.69    inference(subsumption_resolution,[],[f2040,f376])).
% 2.17/0.69  fof(f376,plain,(
% 2.17/0.69    sP2(sK7,sK5,sK4,sK3) | ~spl15_12),
% 2.17/0.69    inference(avatar_component_clause,[],[f375])).
% 2.17/0.69  fof(f2040,plain,(
% 2.17/0.69    m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) | ~sP2(sK7,sK5,sK4,sK3)),
% 2.17/0.69    inference(resolution,[],[f462,f105])).
% 2.17/0.69  fof(f105,plain,(
% 2.17/0.69    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.17/0.69    inference(definition_unfolding,[],[f61,f79])).
% 2.17/0.69  fof(f79,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f9])).
% 2.17/0.69  fof(f9,axiom,(
% 2.17/0.69    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.17/0.69  fof(f61,plain,(
% 2.17/0.69    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.17/0.69    inference(cnf_transformation,[],[f36])).
% 2.17/0.69  fof(f36,plain,(
% 2.17/0.69    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.17/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f35])).
% 2.17/0.69  fof(f35,plain,(
% 2.17/0.69    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK6 != k7_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 2.17/0.69    introduced(choice_axiom,[])).
% 2.17/0.69  fof(f20,plain,(
% 2.17/0.69    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.17/0.69    inference(flattening,[],[f19])).
% 2.17/0.69  fof(f19,plain,(
% 2.17/0.69    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.17/0.69    inference(ennf_transformation,[],[f18])).
% 2.17/0.69  fof(f18,negated_conjecture,(
% 2.17/0.69    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.17/0.69    inference(negated_conjecture,[],[f17])).
% 2.17/0.69  fof(f17,conjecture,(
% 2.17/0.69    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 2.17/0.69  fof(f462,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1) | ~sP2(X3,X2,X1,X0)) )),
% 2.17/0.69    inference(superposition,[],[f111,f97])).
% 2.17/0.69  fof(f97,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) | ~sP2(X0,X1,X2,X3)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f58])).
% 2.17/0.69  fof(f58,plain,(
% 2.17/0.69    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP2(X0,X1,X2,X3))),
% 2.17/0.69    inference(rectify,[],[f57])).
% 2.17/0.69  fof(f57,plain,(
% 2.17/0.69    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 2.17/0.69    inference(nnf_transformation,[],[f33])).
% 2.17/0.69  fof(f33,plain,(
% 2.17/0.69    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 2.17/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.17/0.69  fof(f111,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.17/0.69    inference(definition_unfolding,[],[f101,f79])).
% 2.17/0.69  fof(f101,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.17/0.69    inference(cnf_transformation,[],[f27])).
% 2.17/0.69  fof(f27,plain,(
% 2.17/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.17/0.69    inference(ennf_transformation,[],[f11])).
% 2.17/0.69  fof(f11,axiom,(
% 2.17/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 2.17/0.69  fof(f2107,plain,(
% 2.17/0.69    ( ! [X6,X5] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) | ~sP0(k1_mcart_1(sK7),X5,X6)) ) | (spl15_13 | ~spl15_18 | ~spl15_43)),
% 2.17/0.69    inference(subsumption_resolution,[],[f2106,f1863])).
% 2.17/0.69  fof(f1863,plain,(
% 2.17/0.69    m1_subset_1(k2_mcart_1(sK7),sK5) | ~spl15_43),
% 2.17/0.69    inference(avatar_component_clause,[],[f1861])).
% 2.17/0.69  fof(f2106,plain,(
% 2.17/0.69    ( ! [X6,X5] : (~m1_subset_1(k2_mcart_1(sK7),sK5) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) | ~sP0(k1_mcart_1(sK7),X5,X6)) ) | (spl15_13 | ~spl15_18)),
% 2.17/0.69    inference(subsumption_resolution,[],[f1034,f381])).
% 2.17/0.69  fof(f381,plain,(
% 2.17/0.69    sK6 != k2_mcart_1(sK7) | spl15_13),
% 2.17/0.69    inference(avatar_component_clause,[],[f379])).
% 2.17/0.69  fof(f1034,plain,(
% 2.17/0.69    ( ! [X6,X5] : (sK6 = k2_mcart_1(sK7) | ~m1_subset_1(k2_mcart_1(sK7),sK5) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) | ~sP0(k1_mcart_1(sK7),X5,X6)) ) | ~spl15_18),
% 2.17/0.69    inference(trivial_inequality_removal,[],[f1031])).
% 2.17/0.69  fof(f1031,plain,(
% 2.17/0.69    ( ! [X6,X5] : (sK7 != sK7 | sK6 = k2_mcart_1(sK7) | ~m1_subset_1(k2_mcart_1(sK7),sK5) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) | ~sP0(k1_mcart_1(sK7),X5,X6)) ) | ~spl15_18),
% 2.17/0.69    inference(superposition,[],[f1029,f408])).
% 2.17/0.69  fof(f408,plain,(
% 2.17/0.69    sK7 = k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) | ~spl15_18),
% 2.17/0.69    inference(avatar_component_clause,[],[f406])).
% 2.17/0.69  fof(f1029,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (sK7 != k4_tarski(X0,X3) | sK6 = X3 | ~m1_subset_1(X3,sK5) | ~m1_subset_1(k1_mcart_1(X0),sK3) | ~m1_subset_1(k2_mcart_1(X0),sK4) | ~sP0(X0,X1,X2)) )),
% 2.17/0.69    inference(duplicate_literal_removal,[],[f1028])).
% 2.17/0.69  fof(f1028,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k1_mcart_1(X0),sK3) | sK6 = X3 | ~m1_subset_1(X3,sK5) | sK7 != k4_tarski(X0,X3) | ~m1_subset_1(k2_mcart_1(X0),sK4) | ~sP0(X0,X1,X2) | ~sP0(X0,X1,X2)) )),
% 2.17/0.69    inference(superposition,[],[f942,f542])).
% 2.17/0.69  fof(f542,plain,(
% 2.17/0.69    ( ! [X23,X21,X22] : (sK11(X21,X22,X23) = k1_mcart_1(X21) | ~sP0(X21,X22,X23)) )),
% 2.17/0.69    inference(superposition,[],[f70,f88])).
% 2.17/0.69  fof(f88,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f53])).
% 2.17/0.69  fof(f53,plain,(
% 2.17/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 2.17/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f51,f52])).
% 2.17/0.69  fof(f52,plain,(
% 2.17/0.69    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) = X0 & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X2)))),
% 2.17/0.69    introduced(choice_axiom,[])).
% 2.17/0.69  fof(f51,plain,(
% 2.17/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 2.17/0.69    inference(rectify,[],[f50])).
% 2.17/0.69  fof(f50,plain,(
% 2.17/0.69    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 2.17/0.69    inference(nnf_transformation,[],[f30])).
% 2.17/0.69  fof(f70,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.17/0.69    inference(cnf_transformation,[],[f16])).
% 2.17/0.69  fof(f16,axiom,(
% 2.17/0.69    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 2.17/0.69  fof(f942,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK11(X0,X1,X2),sK3) | sK6 = X3 | ~m1_subset_1(X3,sK5) | sK7 != k4_tarski(X0,X3) | ~m1_subset_1(k2_mcart_1(X0),sK4) | ~sP0(X0,X1,X2)) )),
% 2.17/0.69    inference(duplicate_literal_removal,[],[f937])).
% 2.17/0.69  fof(f937,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK4) | sK6 = X3 | ~m1_subset_1(X3,sK5) | sK7 != k4_tarski(X0,X3) | ~m1_subset_1(sK11(X0,X1,X2),sK3) | ~sP0(X0,X1,X2) | ~sP0(X0,X1,X2)) )),
% 2.17/0.69    inference(superposition,[],[f540,f541])).
% 2.17/0.69  fof(f541,plain,(
% 2.17/0.69    ( ! [X19,X20,X18] : (sK12(X18,X19,X20) = k2_mcart_1(X18) | ~sP0(X18,X19,X20)) )),
% 2.17/0.69    inference(superposition,[],[f71,f88])).
% 2.17/0.70  fof(f71,plain,(
% 2.17/0.70    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.17/0.70    inference(cnf_transformation,[],[f16])).
% 2.17/0.70  fof(f540,plain,(
% 2.17/0.70    ( ! [X14,X17,X15,X16] : (~m1_subset_1(sK12(X14,X15,X16),sK4) | sK6 = X17 | ~m1_subset_1(X17,sK5) | sK7 != k4_tarski(X14,X17) | ~m1_subset_1(sK11(X14,X15,X16),sK3) | ~sP0(X14,X15,X16)) )),
% 2.17/0.70    inference(superposition,[],[f104,f88])).
% 2.17/0.70  fof(f104,plain,(
% 2.17/0.70    ( ! [X6,X7,X5] : (sK7 != k4_tarski(k4_tarski(X5,X6),X7) | sK6 = X7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.17/0.70    inference(definition_unfolding,[],[f62,f78])).
% 2.17/0.70  fof(f78,plain,(
% 2.17/0.70    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f8])).
% 2.17/0.70  fof(f8,axiom,(
% 2.17/0.70    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.17/0.70  fof(f62,plain,(
% 2.17/0.70    ( ! [X6,X7,X5] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f36])).
% 2.17/0.70  fof(f2092,plain,(
% 2.17/0.70    spl15_23 | ~spl15_12),
% 2.17/0.70    inference(avatar_split_clause,[],[f2091,f375,f457])).
% 2.17/0.70  fof(f2091,plain,(
% 2.17/0.70    m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~spl15_12),
% 2.17/0.70    inference(subsumption_resolution,[],[f2073,f376])).
% 2.17/0.70  fof(f2073,plain,(
% 2.17/0.70    m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~sP2(sK7,sK5,sK4,sK3)),
% 2.17/0.70    inference(resolution,[],[f503,f105])).
% 2.17/0.70  fof(f503,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0) | ~sP2(X3,X2,X1,X0)) )),
% 2.17/0.70    inference(superposition,[],[f112,f96])).
% 2.17/0.70  fof(f96,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) | ~sP2(X0,X1,X2,X3)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f58])).
% 2.17/0.70  fof(f112,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.17/0.70    inference(definition_unfolding,[],[f102,f79])).
% 2.17/0.70  fof(f102,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.17/0.70    inference(cnf_transformation,[],[f28])).
% 2.17/0.70  fof(f28,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.17/0.70    inference(ennf_transformation,[],[f10])).
% 2.17/0.70  fof(f10,axiom,(
% 2.17/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 2.17/0.70  fof(f2065,plain,(
% 2.17/0.70    spl15_16 | spl15_18 | ~spl15_1),
% 2.17/0.70    inference(avatar_split_clause,[],[f2064,f131,f406,f396])).
% 2.17/0.70  fof(f396,plain,(
% 2.17/0.70    spl15_16 <=> ! [X1,X0] : ~r2_hidden(sK7,k2_zfmisc_1(X0,X1))),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).
% 2.17/0.70  fof(f2064,plain,(
% 2.17/0.70    ( ! [X0,X1] : (sK7 = k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) | ~r2_hidden(sK7,k2_zfmisc_1(X0,X1))) ) | ~spl15_1),
% 2.17/0.70    inference(forward_demodulation,[],[f2063,f353])).
% 2.17/0.70  fof(f353,plain,(
% 2.17/0.70    sK14(sK7) = k2_mcart_1(sK7) | ~spl15_1),
% 2.17/0.70    inference(resolution,[],[f133,f227])).
% 2.17/0.70  fof(f227,plain,(
% 2.17/0.70    ( ! [X6,X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(X5,X6)) | sK14(X4) = k2_mcart_1(X4)) )),
% 2.17/0.70    inference(superposition,[],[f71,f100])).
% 2.17/0.70  fof(f100,plain,(
% 2.17/0.70    ( ! [X2,X0,X1] : (k4_tarski(sK13(X0),sK14(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.17/0.70    inference(cnf_transformation,[],[f60])).
% 2.17/0.70  fof(f60,plain,(
% 2.17/0.70    ! [X0,X1,X2] : (k4_tarski(sK13(X0),sK14(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.17/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f26,f59])).
% 2.17/0.70  fof(f59,plain,(
% 2.17/0.70    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK13(X0),sK14(X0)) = X0)),
% 2.17/0.70    introduced(choice_axiom,[])).
% 2.17/0.70  fof(f26,plain,(
% 2.17/0.70    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.17/0.70    inference(ennf_transformation,[],[f4])).
% 2.17/0.70  fof(f4,axiom,(
% 2.17/0.70    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 2.17/0.70  fof(f2063,plain,(
% 2.17/0.70    ( ! [X0,X1] : (sK7 = k4_tarski(k1_mcart_1(sK7),sK14(sK7)) | ~r2_hidden(sK7,k2_zfmisc_1(X0,X1))) ) | ~spl15_1),
% 2.17/0.70    inference(superposition,[],[f100,f352])).
% 2.17/0.70  fof(f352,plain,(
% 2.17/0.70    k1_mcart_1(sK7) = sK13(sK7) | ~spl15_1),
% 2.17/0.70    inference(resolution,[],[f133,f228])).
% 2.17/0.70  fof(f228,plain,(
% 2.17/0.70    ( ! [X8,X7,X9] : (~r2_hidden(X7,k2_zfmisc_1(X8,X9)) | k1_mcart_1(X7) = sK13(X7)) )),
% 2.17/0.70    inference(superposition,[],[f70,f100])).
% 2.17/0.70  fof(f1869,plain,(
% 2.17/0.70    spl15_43 | ~spl15_12),
% 2.17/0.70    inference(avatar_split_clause,[],[f1856,f375,f1861])).
% 2.17/0.70  fof(f1856,plain,(
% 2.17/0.70    m1_subset_1(k2_mcart_1(sK7),sK5) | ~spl15_12),
% 2.17/0.70    inference(subsumption_resolution,[],[f1838,f376])).
% 2.17/0.70  fof(f1838,plain,(
% 2.17/0.70    m1_subset_1(k2_mcart_1(sK7),sK5) | ~sP2(sK7,sK5,sK4,sK3)),
% 2.17/0.70    inference(resolution,[],[f515,f105])).
% 2.17/0.70  fof(f515,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k2_mcart_1(X3),X2) | ~sP2(X3,X2,X1,X0)) )),
% 2.17/0.70    inference(superposition,[],[f113,f98])).
% 2.17/0.70  fof(f98,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) | ~sP2(X0,X1,X2,X3)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f58])).
% 2.17/0.70  fof(f113,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.17/0.70    inference(definition_unfolding,[],[f103,f79])).
% 2.17/0.70  fof(f103,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.17/0.70    inference(cnf_transformation,[],[f29])).
% 2.17/0.70  fof(f29,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.17/0.70    inference(ennf_transformation,[],[f12])).
% 2.17/0.70  fof(f12,axiom,(
% 2.17/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 2.17/0.70  fof(f669,plain,(
% 2.17/0.70    spl15_12),
% 2.17/0.70    inference(avatar_split_clause,[],[f668,f375])).
% 2.17/0.70  fof(f668,plain,(
% 2.17/0.70    sP2(sK7,sK5,sK4,sK3)),
% 2.17/0.70    inference(subsumption_resolution,[],[f667,f63])).
% 2.17/0.70  fof(f63,plain,(
% 2.17/0.70    k1_xboole_0 != sK3),
% 2.17/0.70    inference(cnf_transformation,[],[f36])).
% 2.17/0.70  fof(f667,plain,(
% 2.17/0.70    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK3),
% 2.17/0.70    inference(subsumption_resolution,[],[f666,f64])).
% 2.17/0.70  fof(f64,plain,(
% 2.17/0.70    k1_xboole_0 != sK4),
% 2.17/0.70    inference(cnf_transformation,[],[f36])).
% 2.17/0.70  fof(f666,plain,(
% 2.17/0.70    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 2.17/0.70    inference(subsumption_resolution,[],[f650,f65])).
% 2.17/0.70  fof(f65,plain,(
% 2.17/0.70    k1_xboole_0 != sK5),
% 2.17/0.70    inference(cnf_transformation,[],[f36])).
% 2.17/0.70  fof(f650,plain,(
% 2.17/0.70    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 2.17/0.70    inference(resolution,[],[f110,f105])).
% 2.17/0.70  fof(f110,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP2(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.17/0.70    inference(definition_unfolding,[],[f99,f79])).
% 2.17/0.70  fof(f99,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.17/0.70    inference(cnf_transformation,[],[f34])).
% 2.17/0.70  fof(f34,plain,(
% 2.17/0.70    ! [X0,X1,X2] : (! [X3] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.17/0.70    inference(definition_folding,[],[f25,f33])).
% 2.17/0.70  fof(f25,plain,(
% 2.17/0.70    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.17/0.70    inference(ennf_transformation,[],[f15])).
% 2.17/0.70  fof(f15,axiom,(
% 2.17/0.70    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.17/0.70  fof(f644,plain,(
% 2.17/0.70    ~spl15_8),
% 2.17/0.70    inference(avatar_contradiction_clause,[],[f643])).
% 2.17/0.70  fof(f643,plain,(
% 2.17/0.70    $false | ~spl15_8),
% 2.17/0.70    inference(subsumption_resolution,[],[f640,f64])).
% 2.17/0.70  fof(f640,plain,(
% 2.17/0.70    k1_xboole_0 = sK4 | ~spl15_8),
% 2.17/0.70    inference(resolution,[],[f614,f121])).
% 2.17/0.70  fof(f121,plain,(
% 2.17/0.70    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.17/0.70    inference(superposition,[],[f69,f114])).
% 2.17/0.70  fof(f114,plain,(
% 2.17/0.70    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.17/0.70    inference(equality_resolution,[],[f77])).
% 2.17/0.70  fof(f77,plain,(
% 2.17/0.70    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.17/0.70    inference(cnf_transformation,[],[f45])).
% 2.17/0.70  fof(f45,plain,(
% 2.17/0.70    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.17/0.70    inference(flattening,[],[f44])).
% 2.17/0.70  fof(f44,plain,(
% 2.17/0.70    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.17/0.70    inference(nnf_transformation,[],[f5])).
% 2.17/0.70  fof(f5,axiom,(
% 2.17/0.70    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.17/0.70  fof(f69,plain,(
% 2.17/0.70    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.17/0.70    inference(cnf_transformation,[],[f6])).
% 2.17/0.70  fof(f6,axiom,(
% 2.17/0.70    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 2.17/0.70  fof(f614,plain,(
% 2.17/0.70    ( ! [X1] : (r2_hidden(sK9(X1,sK4),X1) | sK4 = X1) ) | ~spl15_8),
% 2.17/0.70    inference(resolution,[],[f344,f73])).
% 2.17/0.70  fof(f73,plain,(
% 2.17/0.70    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | X0 = X1 | r2_hidden(sK9(X0,X1),X0)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f43])).
% 2.17/0.70  fof(f43,plain,(
% 2.17/0.70    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 2.17/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).
% 2.17/0.70  fof(f42,plain,(
% 2.17/0.70    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 2.17/0.70    introduced(choice_axiom,[])).
% 2.17/0.70  fof(f41,plain,(
% 2.17/0.70    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.17/0.70    inference(nnf_transformation,[],[f23])).
% 2.17/0.70  fof(f23,plain,(
% 2.17/0.70    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.17/0.70    inference(ennf_transformation,[],[f2])).
% 2.17/0.70  fof(f2,axiom,(
% 2.17/0.70    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 2.17/0.70  fof(f344,plain,(
% 2.17/0.70    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | ~spl15_8),
% 2.17/0.70    inference(avatar_component_clause,[],[f343])).
% 2.17/0.70  fof(f343,plain,(
% 2.17/0.70    spl15_8 <=> ! [X0] : ~r2_hidden(X0,sK4)),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).
% 2.17/0.70  fof(f611,plain,(
% 2.17/0.70    spl15_7 | spl15_8 | ~spl15_6),
% 2.17/0.70    inference(avatar_split_clause,[],[f505,f290,f343,f340])).
% 2.17/0.70  fof(f340,plain,(
% 2.17/0.70    spl15_7 <=> ! [X1] : ~r2_hidden(X1,sK3)),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).
% 2.17/0.70  fof(f290,plain,(
% 2.17/0.70    spl15_6 <=> ! [X0] : ~r2_hidden(X0,k2_zfmisc_1(sK3,sK4))),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).
% 2.17/0.70  fof(f505,plain,(
% 2.17/0.70    ( ! [X0,X1] : (~r2_hidden(X0,sK4) | ~r2_hidden(X1,sK3)) ) | ~spl15_6),
% 2.17/0.70    inference(resolution,[],[f328,f116])).
% 2.17/0.70  fof(f116,plain,(
% 2.17/0.70    ( ! [X4,X2,X3,X1] : (sP0(k4_tarski(X3,X4),X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 2.17/0.70    inference(equality_resolution,[],[f89])).
% 2.17/0.70  fof(f89,plain,(
% 2.17/0.70    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2) | k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f53])).
% 2.17/0.70  fof(f328,plain,(
% 2.17/0.70    ( ! [X0] : (~sP0(X0,sK4,sK3)) ) | ~spl15_6),
% 2.17/0.70    inference(resolution,[],[f291,f206])).
% 2.17/0.70  fof(f206,plain,(
% 2.17/0.70    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_zfmisc_1(X2,X1)) | ~sP0(X0,X1,X2)) )),
% 2.17/0.70    inference(resolution,[],[f83,f117])).
% 2.17/0.70  fof(f83,plain,(
% 2.17/0.70    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f49])).
% 2.17/0.70  fof(f291,plain,(
% 2.17/0.70    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK3,sK4))) ) | ~spl15_6),
% 2.17/0.70    inference(avatar_component_clause,[],[f290])).
% 2.17/0.70  fof(f609,plain,(
% 2.17/0.70    ~spl15_7),
% 2.17/0.70    inference(avatar_contradiction_clause,[],[f608])).
% 2.17/0.70  fof(f608,plain,(
% 2.17/0.70    $false | ~spl15_7),
% 2.17/0.70    inference(subsumption_resolution,[],[f605,f63])).
% 2.17/0.70  fof(f605,plain,(
% 2.17/0.70    k1_xboole_0 = sK3 | ~spl15_7),
% 2.17/0.70    inference(resolution,[],[f499,f121])).
% 2.17/0.70  fof(f499,plain,(
% 2.17/0.70    ( ! [X1] : (r2_hidden(sK9(X1,sK3),X1) | sK3 = X1) ) | ~spl15_7),
% 2.17/0.70    inference(resolution,[],[f341,f73])).
% 2.17/0.70  fof(f341,plain,(
% 2.17/0.70    ( ! [X1] : (~r2_hidden(X1,sK3)) ) | ~spl15_7),
% 2.17/0.70    inference(avatar_component_clause,[],[f340])).
% 2.17/0.70  fof(f415,plain,(
% 2.17/0.70    ~spl15_1 | ~spl15_16),
% 2.17/0.70    inference(avatar_contradiction_clause,[],[f410])).
% 2.17/0.70  fof(f410,plain,(
% 2.17/0.70    $false | (~spl15_1 | ~spl15_16)),
% 2.17/0.70    inference(subsumption_resolution,[],[f133,f397])).
% 2.17/0.70  fof(f397,plain,(
% 2.17/0.70    ( ! [X0,X1] : (~r2_hidden(sK7,k2_zfmisc_1(X0,X1))) ) | ~spl15_16),
% 2.17/0.70    inference(avatar_component_clause,[],[f396])).
% 2.17/0.70  fof(f382,plain,(
% 2.17/0.70    ~spl15_12 | ~spl15_13),
% 2.17/0.70    inference(avatar_split_clause,[],[f373,f379,f375])).
% 2.17/0.70  fof(f373,plain,(
% 2.17/0.70    sK6 != k2_mcart_1(sK7) | ~sP2(sK7,sK5,sK4,sK3)),
% 2.17/0.70    inference(superposition,[],[f66,f98])).
% 2.17/0.70  fof(f66,plain,(
% 2.17/0.70    sK6 != k7_mcart_1(sK3,sK4,sK5,sK7)),
% 2.17/0.70    inference(cnf_transformation,[],[f36])).
% 2.17/0.70  fof(f327,plain,(
% 2.17/0.70    ~spl15_5),
% 2.17/0.70    inference(avatar_contradiction_clause,[],[f326])).
% 2.17/0.70  fof(f326,plain,(
% 2.17/0.70    $false | ~spl15_5),
% 2.17/0.70    inference(subsumption_resolution,[],[f324,f65])).
% 2.17/0.70  fof(f324,plain,(
% 2.17/0.70    k1_xboole_0 = sK5 | ~spl15_5),
% 2.17/0.70    inference(resolution,[],[f305,f121])).
% 2.17/0.70  fof(f305,plain,(
% 2.17/0.70    ( ! [X22] : (r2_hidden(sK9(X22,sK5),X22) | sK5 = X22) ) | ~spl15_5),
% 2.17/0.70    inference(resolution,[],[f73,f288])).
% 2.17/0.70  fof(f288,plain,(
% 2.17/0.70    ( ! [X1] : (~r2_hidden(X1,sK5)) ) | ~spl15_5),
% 2.17/0.70    inference(avatar_component_clause,[],[f287])).
% 2.17/0.70  fof(f287,plain,(
% 2.17/0.70    spl15_5 <=> ! [X1] : ~r2_hidden(X1,sK5)),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).
% 2.17/0.70  fof(f292,plain,(
% 2.17/0.70    spl15_5 | spl15_6 | ~spl15_2),
% 2.17/0.70    inference(avatar_split_clause,[],[f278,f135,f290,f287])).
% 2.17/0.70  fof(f135,plain,(
% 2.17/0.70    spl15_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 2.17/0.70  fof(f278,plain,(
% 2.17/0.70    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) | ~r2_hidden(X1,sK5)) ) | ~spl15_2),
% 2.17/0.70    inference(resolution,[],[f254,f137])).
% 2.17/0.70  fof(f137,plain,(
% 2.17/0.70    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl15_2),
% 2.17/0.70    inference(avatar_component_clause,[],[f135])).
% 2.17/0.70  fof(f254,plain,(
% 2.17/0.70    ( ! [X6,X4,X5,X3] : (~v1_xboole_0(k2_zfmisc_1(X6,X4)) | ~r2_hidden(X5,X6) | ~r2_hidden(X3,X4)) )),
% 2.17/0.70    inference(resolution,[],[f116,f213])).
% 2.17/0.70  fof(f213,plain,(
% 2.17/0.70    ( ! [X12,X13,X11] : (~sP0(X11,X12,X13) | ~v1_xboole_0(k2_zfmisc_1(X13,X12))) )),
% 2.17/0.70    inference(resolution,[],[f206,f67])).
% 2.17/0.70  fof(f67,plain,(
% 2.17/0.70    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f40])).
% 2.17/0.70  fof(f40,plain,(
% 2.17/0.70    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.17/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).
% 2.17/0.70  fof(f39,plain,(
% 2.17/0.70    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 2.17/0.70    introduced(choice_axiom,[])).
% 2.17/0.70  fof(f38,plain,(
% 2.17/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.17/0.70    inference(rectify,[],[f37])).
% 2.17/0.70  fof(f37,plain,(
% 2.17/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.17/0.70    inference(nnf_transformation,[],[f1])).
% 2.17/0.70  fof(f1,axiom,(
% 2.17/0.70    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.17/0.70  fof(f138,plain,(
% 2.17/0.70    spl15_1 | spl15_2),
% 2.17/0.70    inference(avatar_split_clause,[],[f129,f135,f131])).
% 2.17/0.70  fof(f129,plain,(
% 2.17/0.70    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.17/0.70    inference(resolution,[],[f72,f105])).
% 2.17/0.70  fof(f72,plain,(
% 2.17/0.70    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f22])).
% 2.17/0.70  fof(f22,plain,(
% 2.17/0.70    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.17/0.70    inference(flattening,[],[f21])).
% 2.17/0.70  fof(f21,plain,(
% 2.17/0.70    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.17/0.70    inference(ennf_transformation,[],[f7])).
% 2.17/0.70  fof(f7,axiom,(
% 2.17/0.70    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.17/0.70  % SZS output end Proof for theBenchmark
% 2.17/0.70  % (12001)------------------------------
% 2.17/0.70  % (12001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.70  % (12001)Termination reason: Refutation
% 2.17/0.70  
% 2.17/0.70  % (12001)Memory used [KB]: 7036
% 2.17/0.70  % (12001)Time elapsed: 0.278 s
% 2.17/0.70  % (12001)------------------------------
% 2.17/0.70  % (12001)------------------------------
% 2.17/0.70  % (11973)Success in time 0.338 s
%------------------------------------------------------------------------------
