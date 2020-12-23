%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 397 expanded)
%              Number of leaves         :   36 ( 151 expanded)
%              Depth                    :   16
%              Number of atoms          :  609 (1873 expanded)
%              Number of equality atoms :  314 (1080 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f867,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f126,f307,f330,f344,f359,f373,f414,f636,f655,f673,f681,f828,f829,f866])).

fof(f866,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_9 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_9 ),
    inference(unit_resulting_resolution,[],[f95,f100,f105,f110,f321,f260])).

fof(f260,plain,(
    ! [X24,X23,X21,X22] :
      ( k7_mcart_1(X21,X22,X23,X24) = k2_mcart_1(X24)
      | ~ m1_subset_1(X24,k2_zfmisc_1(k2_zfmisc_1(X21,X22),X23))
      | k1_xboole_0 = X23
      | k1_xboole_0 = X22
      | k1_xboole_0 = X21 ) ),
    inference(superposition,[],[f64,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f48,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f64,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f321,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
    | spl11_9 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl11_9
  <=> k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f110,plain,
    ( m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl11_4
  <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f105,plain,
    ( k1_xboole_0 != sK2
    | spl11_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl11_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f100,plain,
    ( k1_xboole_0 != sK1
    | spl11_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl11_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f95,plain,
    ( k1_xboole_0 != sK0
    | spl11_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl11_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f829,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
    | k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) != k1_mcart_1(sK3)
    | sK3 != k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f828,plain,
    ( spl11_26
    | ~ spl11_27
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(avatar_split_clause,[],[f822,f454,f370,f633,f629])).

fof(f629,plain,
    ( spl11_26
  <=> k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f633,plain,
    ( spl11_27
  <=> r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f370,plain,
    ( spl11_13
  <=> k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = k1_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f454,plain,
    ( spl11_21
  <=> sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f822,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3)
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(equality_resolution,[],[f805])).

fof(f805,plain,
    ( ! [X50] :
        ( sK3 != X50
        | ~ r2_hidden(sK3,k1_enumset1(X50,X50,sK3))
        | k1_xboole_0 = k1_enumset1(X50,X50,sK3) )
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(duplicate_literal_removal,[],[f802])).

fof(f802,plain,
    ( ! [X50] :
        ( sK3 != X50
        | ~ r2_hidden(sK3,k1_enumset1(X50,X50,sK3))
        | k1_xboole_0 = k1_enumset1(X50,X50,sK3)
        | k1_xboole_0 = k1_enumset1(X50,X50,sK3)
        | ~ r2_hidden(sK3,k1_enumset1(X50,X50,sK3)) )
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(superposition,[],[f753,f784])).

fof(f784,plain,
    ( ! [X0] :
        ( sK4(k1_enumset1(X0,X0,sK3)) = X0
        | k1_xboole_0 = k1_enumset1(X0,X0,sK3)
        | ~ r2_hidden(sK3,k1_enumset1(X0,X0,sK3)) )
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(equality_resolution,[],[f756])).

fof(f756,plain,
    ( ! [X0,X1] :
        ( sK3 != X1
        | ~ r2_hidden(sK3,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) = k1_xboole_0
        | sK4(k1_enumset1(X0,X0,X1)) = X0 )
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(duplicate_literal_removal,[],[f755])).

fof(f755,plain,
    ( ! [X0,X1] :
        ( sK3 != X1
        | ~ r2_hidden(sK3,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) = k1_xboole_0
        | sK4(k1_enumset1(X0,X0,X1)) = X0
        | k1_enumset1(X0,X0,X1) = k1_xboole_0 )
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(superposition,[],[f753,f131])).

fof(f131,plain,(
    ! [X4,X5] :
      ( sK4(k1_enumset1(X4,X4,X5)) = X5
      | sK4(k1_enumset1(X4,X4,X5)) = X4
      | k1_xboole_0 = k1_enumset1(X4,X4,X5) ) ),
    inference(resolution,[],[f89,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK10(X0,X1,X2) != X1
              & sK10(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sK10(X0,X1,X2) = X1
            | sK10(X0,X1,X2) = X0
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK10(X0,X1,X2) != X1
            & sK10(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sK10(X0,X1,X2) = X1
          | sK10(X0,X1,X2) = X0
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f753,plain,
    ( ! [X0] :
        ( sK3 != sK4(X0)
        | ~ r2_hidden(sK3,X0)
        | k1_xboole_0 = X0 )
    | ~ spl11_13
    | ~ spl11_21 ),
    inference(superposition,[],[f702,f456])).

fof(f456,plain,
    ( sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f454])).

fof(f702,plain,
    ( ! [X4,X3] :
        ( sK4(X3) != k4_tarski(k1_mcart_1(sK3),X4)
        | ~ r2_hidden(sK3,X3)
        | k1_xboole_0 = X3 )
    | ~ spl11_13 ),
    inference(superposition,[],[f70,f372])).

fof(f372,plain,
    ( k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = k1_mcart_1(sK3)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f370])).

fof(f70,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f681,plain,(
    ~ spl11_28 ),
    inference(avatar_contradiction_clause,[],[f678])).

fof(f678,plain,
    ( $false
    | ~ spl11_28 ),
    inference(unit_resulting_resolution,[],[f223,f671])).

fof(f671,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f669])).

fof(f669,plain,
    ( spl11_28
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f223,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(global_subsumption,[],[f165,f186])).

fof(f186,plain,(
    ! [X2,X1] :
      ( k1_mcart_1(X2) != X1
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f112,f165])).

fof(f112,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f90,f64])).

fof(f90,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f165,plain,(
    ! [X2,X0] :
      ( k1_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(condensation,[],[f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(resolution,[],[f157,f89])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_mcart_1(X1),X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f149,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f149,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X6,X7))
      | r2_hidden(k1_mcart_1(X8),X6) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(k1_mcart_1(X8),X6)
      | ~ r2_hidden(X8,k2_zfmisc_1(X6,X7))
      | ~ r2_hidden(X8,k2_zfmisc_1(X6,X7)) ) ),
    inference(superposition,[],[f84,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( sK8(X0,X1,X2) = k1_mcart_1(X2)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f63,f82])).

fof(f82,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
              & r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
                & r2_hidden(sK9(X0,X1,X8),X1)
                & r2_hidden(sK8(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
        & r2_hidden(sK9(X0,X1,X8),X1)
        & r2_hidden(sK8(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f673,plain,
    ( spl11_28
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f662,f629,f669])).

fof(f662,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl11_26 ),
    inference(superposition,[],[f86,f631])).

fof(f631,plain,
    ( k1_xboole_0 = k1_enumset1(sK3,sK3,sK3)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f629])).

fof(f86,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f655,plain,(
    spl11_27 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | spl11_27 ),
    inference(unit_resulting_resolution,[],[f86,f635])).

fof(f635,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | spl11_27 ),
    inference(avatar_component_clause,[],[f633])).

fof(f636,plain,
    ( spl11_26
    | ~ spl11_27
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f627,f411,f633,f629])).

fof(f411,plain,
    ( spl11_18
  <=> sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f627,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3)
    | ~ spl11_18 ),
    inference(equality_resolution,[],[f620])).

fof(f620,plain,
    ( ! [X20] :
        ( sK3 != X20
        | ~ r2_hidden(sK3,k1_enumset1(X20,X20,sK3))
        | k1_xboole_0 = k1_enumset1(X20,X20,sK3) )
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f597])).

fof(f597,plain,
    ( ! [X20] :
        ( sK3 != X20
        | ~ r2_hidden(sK3,k1_enumset1(X20,X20,sK3))
        | k1_xboole_0 = k1_enumset1(X20,X20,sK3)
        | k1_xboole_0 = k1_enumset1(X20,X20,sK3)
        | ~ r2_hidden(sK3,k1_enumset1(X20,X20,sK3)) )
    | ~ spl11_18 ),
    inference(superposition,[],[f415,f589])).

fof(f589,plain,
    ( ! [X0] :
        ( sK4(k1_enumset1(X0,X0,sK3)) = X0
        | k1_xboole_0 = k1_enumset1(X0,X0,sK3)
        | ~ r2_hidden(sK3,k1_enumset1(X0,X0,sK3)) )
    | ~ spl11_18 ),
    inference(equality_resolution,[],[f451])).

fof(f451,plain,
    ( ! [X0,X1] :
        ( sK3 != X1
        | ~ r2_hidden(sK3,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) = k1_xboole_0
        | sK4(k1_enumset1(X0,X0,X1)) = X0 )
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f443])).

fof(f443,plain,
    ( ! [X0,X1] :
        ( sK3 != X1
        | ~ r2_hidden(sK3,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) = k1_xboole_0
        | sK4(k1_enumset1(X0,X0,X1)) = X0
        | k1_enumset1(X0,X0,X1) = k1_xboole_0 )
    | ~ spl11_18 ),
    inference(superposition,[],[f415,f131])).

fof(f415,plain,
    ( ! [X0] :
        ( sK3 != sK4(X0)
        | ~ r2_hidden(sK3,X0)
        | k1_xboole_0 = X0 )
    | ~ spl11_18 ),
    inference(superposition,[],[f71,f413])).

fof(f413,plain,
    ( sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f411])).

fof(f71,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f46,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f414,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_18
    | ~ spl11_5
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f396,f320,f115,f411,f108,f103,f98,f93])).

fof(f115,plain,
    ( spl11_5
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f396,plain,
    ( sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_5
    | ~ spl11_9 ),
    inference(forward_demodulation,[],[f395,f322])).

fof(f322,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f320])).

fof(f395,plain,
    ( sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_5 ),
    inference(superposition,[],[f69,f117])).

fof(f117,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f373,plain,
    ( spl11_13
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f363,f356,f370])).

fof(f356,plain,
    ( spl11_12
  <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f363,plain,
    ( k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = k1_mcart_1(sK3)
    | ~ spl11_12 ),
    inference(superposition,[],[f63,f358])).

fof(f358,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_mcart_1(sK3))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f356])).

fof(f359,plain,
    ( spl11_12
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f354,f320,f304,f356])).

fof(f304,plain,
    ( spl11_8
  <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f354,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_mcart_1(sK3))
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(forward_demodulation,[],[f306,f322])).

fof(f306,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f304])).

fof(f344,plain,(
    ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f112,f329])).

fof(f329,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl11_10
  <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f330,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_10
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f324,f123,f327,f108,f103,f98,f93])).

fof(f123,plain,
    ( spl11_7
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f324,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_7 ),
    inference(superposition,[],[f69,f125])).

fof(f125,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f307,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_8
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f255,f119,f304,f108,f103,f98,f93])).

fof(f119,plain,
    ( spl11_6
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f255,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_6 ),
    inference(superposition,[],[f69,f121])).

fof(f121,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f126,plain,
    ( spl11_5
    | spl11_6
    | spl11_7 ),
    inference(avatar_split_clause,[],[f39,f123,f119,f115])).

fof(f39,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
            | k6_mcart_1(sK0,sK1,sK2,X3) = X3
            | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
          | k6_mcart_1(sK0,sK1,sK2,X3) = X3
          | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f111,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f68,f108])).

fof(f68,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f38,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f106,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f37,f103])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f101,plain,(
    ~ spl11_2 ),
    inference(avatar_split_clause,[],[f36,f98])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f35,f93])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (28415)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (28400)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (28423)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (28425)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (28407)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (28408)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (28422)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (28414)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (28409)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (28412)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (28417)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (28401)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (28414)Refutation not found, incomplete strategy% (28414)------------------------------
% 0.20/0.52  % (28414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28414)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28414)Memory used [KB]: 1791
% 0.20/0.52  % (28414)Time elapsed: 0.079 s
% 0.20/0.52  % (28414)------------------------------
% 0.20/0.52  % (28414)------------------------------
% 0.20/0.53  % (28402)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (28411)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (28412)Refutation not found, incomplete strategy% (28412)------------------------------
% 0.20/0.53  % (28412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28412)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28412)Memory used [KB]: 10746
% 0.20/0.53  % (28412)Time elapsed: 0.111 s
% 0.20/0.53  % (28412)------------------------------
% 0.20/0.53  % (28412)------------------------------
% 0.20/0.53  % (28404)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (28405)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (28401)Refutation not found, incomplete strategy% (28401)------------------------------
% 0.20/0.53  % (28401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28401)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28401)Memory used [KB]: 1791
% 0.20/0.53  % (28401)Time elapsed: 0.109 s
% 0.20/0.53  % (28401)------------------------------
% 0.20/0.53  % (28401)------------------------------
% 0.20/0.53  % (28403)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (28421)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (28429)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (28420)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (28418)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (28418)Refutation not found, incomplete strategy% (28418)------------------------------
% 0.20/0.54  % (28418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28418)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28418)Memory used [KB]: 1791
% 0.20/0.54  % (28418)Time elapsed: 0.119 s
% 0.20/0.54  % (28418)------------------------------
% 0.20/0.54  % (28418)------------------------------
% 0.20/0.54  % (28416)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (28427)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (28419)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (28413)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (28426)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (28424)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (28410)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (28428)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (28406)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (28429)Refutation not found, incomplete strategy% (28429)------------------------------
% 0.20/0.55  % (28429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28429)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28429)Memory used [KB]: 1663
% 0.20/0.55  % (28429)Time elapsed: 0.144 s
% 0.20/0.55  % (28429)------------------------------
% 0.20/0.55  % (28429)------------------------------
% 0.20/0.56  % (28416)Refutation not found, incomplete strategy% (28416)------------------------------
% 0.20/0.56  % (28416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (28416)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (28416)Memory used [KB]: 10746
% 0.20/0.56  % (28416)Time elapsed: 0.128 s
% 0.20/0.56  % (28416)------------------------------
% 0.20/0.56  % (28416)------------------------------
% 0.20/0.56  % (28428)Refutation not found, incomplete strategy% (28428)------------------------------
% 0.20/0.56  % (28428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (28428)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (28428)Memory used [KB]: 11001
% 0.20/0.56  % (28428)Time elapsed: 0.148 s
% 0.20/0.56  % (28428)------------------------------
% 0.20/0.56  % (28428)------------------------------
% 0.20/0.56  % (28424)Refutation not found, incomplete strategy% (28424)------------------------------
% 0.20/0.56  % (28424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (28424)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (28424)Memory used [KB]: 10746
% 0.20/0.56  % (28424)Time elapsed: 0.147 s
% 0.20/0.56  % (28424)------------------------------
% 0.20/0.56  % (28424)------------------------------
% 0.20/0.57  % (28426)Refutation not found, incomplete strategy% (28426)------------------------------
% 0.20/0.57  % (28426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (28426)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (28426)Memory used [KB]: 6268
% 0.20/0.57  % (28426)Time elapsed: 0.164 s
% 0.20/0.57  % (28426)------------------------------
% 0.20/0.57  % (28426)------------------------------
% 0.20/0.57  % (28410)Refutation not found, incomplete strategy% (28410)------------------------------
% 0.20/0.57  % (28410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (28410)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (28410)Memory used [KB]: 11001
% 0.20/0.57  % (28410)Time elapsed: 0.146 s
% 0.20/0.57  % (28410)------------------------------
% 0.20/0.57  % (28410)------------------------------
% 0.20/0.58  % (28423)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f867,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f126,f307,f330,f344,f359,f373,f414,f636,f655,f673,f681,f828,f829,f866])).
% 0.20/0.58  fof(f866,plain,(
% 0.20/0.58    spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_9),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f863])).
% 0.20/0.58  fof(f863,plain,(
% 0.20/0.58    $false | (spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_9)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f95,f100,f105,f110,f321,f260])).
% 0.20/0.58  fof(f260,plain,(
% 0.20/0.58    ( ! [X24,X23,X21,X22] : (k7_mcart_1(X21,X22,X23,X24) = k2_mcart_1(X24) | ~m1_subset_1(X24,k2_zfmisc_1(k2_zfmisc_1(X21,X22),X23)) | k1_xboole_0 = X23 | k1_xboole_0 = X22 | k1_xboole_0 = X21) )),
% 0.20/0.58    inference(superposition,[],[f64,f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f40,f48,f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.58  fof(f321,plain,(
% 0.20/0.58    k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) | spl11_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f320])).
% 0.20/0.58  fof(f320,plain,(
% 0.20/0.58    spl11_9 <=> k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.20/0.58  fof(f110,plain,(
% 0.20/0.58    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl11_4),
% 0.20/0.58    inference(avatar_component_clause,[],[f108])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    spl11_4 <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.20/0.58  fof(f105,plain,(
% 0.20/0.58    k1_xboole_0 != sK2 | spl11_3),
% 0.20/0.58    inference(avatar_component_clause,[],[f103])).
% 0.20/0.58  fof(f103,plain,(
% 0.20/0.58    spl11_3 <=> k1_xboole_0 = sK2),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    k1_xboole_0 != sK1 | spl11_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f98])).
% 0.20/0.58  fof(f98,plain,(
% 0.20/0.58    spl11_2 <=> k1_xboole_0 = sK1),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.20/0.58  fof(f95,plain,(
% 0.20/0.58    k1_xboole_0 != sK0 | spl11_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f93])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    spl11_1 <=> k1_xboole_0 = sK0),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.58  fof(f829,plain,(
% 0.20/0.58    k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) | k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) != k1_mcart_1(sK3) | sK3 != k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3))),
% 0.20/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.58  fof(f828,plain,(
% 0.20/0.58    spl11_26 | ~spl11_27 | ~spl11_13 | ~spl11_21),
% 0.20/0.58    inference(avatar_split_clause,[],[f822,f454,f370,f633,f629])).
% 0.20/0.58  fof(f629,plain,(
% 0.20/0.58    spl11_26 <=> k1_xboole_0 = k1_enumset1(sK3,sK3,sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 0.20/0.58  fof(f633,plain,(
% 0.20/0.58    spl11_27 <=> r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).
% 0.20/0.58  fof(f370,plain,(
% 0.20/0.58    spl11_13 <=> k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = k1_mcart_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.20/0.58  fof(f454,plain,(
% 0.20/0.58    spl11_21 <=> sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 0.20/0.58  fof(f822,plain,(
% 0.20/0.58    ~r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) | (~spl11_13 | ~spl11_21)),
% 0.20/0.58    inference(equality_resolution,[],[f805])).
% 0.20/0.58  fof(f805,plain,(
% 0.20/0.58    ( ! [X50] : (sK3 != X50 | ~r2_hidden(sK3,k1_enumset1(X50,X50,sK3)) | k1_xboole_0 = k1_enumset1(X50,X50,sK3)) ) | (~spl11_13 | ~spl11_21)),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f802])).
% 0.20/0.58  fof(f802,plain,(
% 0.20/0.58    ( ! [X50] : (sK3 != X50 | ~r2_hidden(sK3,k1_enumset1(X50,X50,sK3)) | k1_xboole_0 = k1_enumset1(X50,X50,sK3) | k1_xboole_0 = k1_enumset1(X50,X50,sK3) | ~r2_hidden(sK3,k1_enumset1(X50,X50,sK3))) ) | (~spl11_13 | ~spl11_21)),
% 0.20/0.58    inference(superposition,[],[f753,f784])).
% 0.20/0.58  fof(f784,plain,(
% 0.20/0.58    ( ! [X0] : (sK4(k1_enumset1(X0,X0,sK3)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,sK3) | ~r2_hidden(sK3,k1_enumset1(X0,X0,sK3))) ) | (~spl11_13 | ~spl11_21)),
% 0.20/0.58    inference(equality_resolution,[],[f756])).
% 0.20/0.58  fof(f756,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(sK3,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) = k1_xboole_0 | sK4(k1_enumset1(X0,X0,X1)) = X0) ) | (~spl11_13 | ~spl11_21)),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f755])).
% 0.20/0.58  fof(f755,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(sK3,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) = k1_xboole_0 | sK4(k1_enumset1(X0,X0,X1)) = X0 | k1_enumset1(X0,X0,X1) = k1_xboole_0) ) | (~spl11_13 | ~spl11_21)),
% 0.20/0.58    inference(superposition,[],[f753,f131])).
% 0.20/0.58  fof(f131,plain,(
% 0.20/0.58    ( ! [X4,X5] : (sK4(k1_enumset1(X4,X4,X5)) = X5 | sK4(k1_enumset1(X4,X4,X5)) = X4 | k1_xboole_0 = k1_enumset1(X4,X4,X5)) )),
% 0.20/0.58    inference(resolution,[],[f89,f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f15,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.20/0.58    inference(equality_resolution,[],[f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.58    inference(definition_unfolding,[],[f57,f67])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK10(X0,X1,X2) != X1 & sK10(X0,X1,X2) != X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sK10(X0,X1,X2) = X1 | sK10(X0,X1,X2) = X0 | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f32,f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK10(X0,X1,X2) != X1 & sK10(X0,X1,X2) != X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sK10(X0,X1,X2) = X1 | sK10(X0,X1,X2) = X0 | r2_hidden(sK10(X0,X1,X2),X2))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.58    inference(rectify,[],[f31])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.58    inference(flattening,[],[f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.58    inference(nnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.58  fof(f753,plain,(
% 0.20/0.58    ( ! [X0] : (sK3 != sK4(X0) | ~r2_hidden(sK3,X0) | k1_xboole_0 = X0) ) | (~spl11_13 | ~spl11_21)),
% 0.20/0.58    inference(superposition,[],[f702,f456])).
% 0.20/0.58  fof(f456,plain,(
% 0.20/0.58    sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3)) | ~spl11_21),
% 0.20/0.58    inference(avatar_component_clause,[],[f454])).
% 0.20/0.58  fof(f702,plain,(
% 0.20/0.58    ( ! [X4,X3] : (sK4(X3) != k4_tarski(k1_mcart_1(sK3),X4) | ~r2_hidden(sK3,X3) | k1_xboole_0 = X3) ) | ~spl11_13),
% 0.20/0.58    inference(superposition,[],[f70,f372])).
% 0.20/0.58  fof(f372,plain,(
% 0.20/0.58    k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = k1_mcart_1(sK3) | ~spl11_13),
% 0.20/0.58    inference(avatar_component_clause,[],[f370])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f47,f48])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f23])).
% 0.20/0.58  fof(f681,plain,(
% 0.20/0.58    ~spl11_28),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f678])).
% 0.20/0.58  fof(f678,plain,(
% 0.20/0.58    $false | ~spl11_28),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f223,f671])).
% 0.20/0.58  fof(f671,plain,(
% 0.20/0.58    r2_hidden(sK3,k1_xboole_0) | ~spl11_28),
% 0.20/0.58    inference(avatar_component_clause,[],[f669])).
% 0.20/0.58  fof(f669,plain,(
% 0.20/0.58    spl11_28 <=> r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).
% 0.20/0.58  fof(f223,plain,(
% 0.20/0.58    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.58    inference(global_subsumption,[],[f165,f186])).
% 0.20/0.58  fof(f186,plain,(
% 0.20/0.58    ( ! [X2,X1] : (k1_mcart_1(X2) != X1 | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.58    inference(superposition,[],[f112,f165])).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 0.20/0.58    inference(forward_demodulation,[],[f90,f64])).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.20/0.58    inference(equality_resolution,[],[f66])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.20/0.58  fof(f165,plain,(
% 0.20/0.58    ( ! [X2,X0] : (k1_mcart_1(X0) = X2 | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(condensation,[],[f162])).
% 0.20/0.58  fof(f162,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_xboole_0) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 0.20/0.58    inference(resolution,[],[f157,f89])).
% 0.20/0.58  fof(f157,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X1),X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.58    inference(superposition,[],[f149,f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f44])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.58    inference(flattening,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.58    inference(nnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.58  fof(f149,plain,(
% 0.20/0.58    ( ! [X6,X8,X7] : (~r2_hidden(X8,k2_zfmisc_1(X6,X7)) | r2_hidden(k1_mcart_1(X8),X6)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f148])).
% 0.20/0.58  fof(f148,plain,(
% 0.20/0.58    ( ! [X6,X8,X7] : (r2_hidden(k1_mcart_1(X8),X6) | ~r2_hidden(X8,k2_zfmisc_1(X6,X7)) | ~r2_hidden(X8,k2_zfmisc_1(X6,X7))) )),
% 0.20/0.58    inference(superposition,[],[f84,f136])).
% 0.20/0.58  fof(f136,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sK8(X0,X1,X2) = k1_mcart_1(X2) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.58    inference(superposition,[],[f63,f82])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    ( ! [X0,X8,X1] : (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.58    inference(equality_resolution,[],[f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ( ! [X2,X0,X8,X1] : (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f25,f28,f27,f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.58    inference(rectify,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.58    inference(nnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.58    inference(equality_resolution,[],[f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f673,plain,(
% 0.20/0.58    spl11_28 | ~spl11_26),
% 0.20/0.58    inference(avatar_split_clause,[],[f662,f629,f669])).
% 0.20/0.58  fof(f662,plain,(
% 0.20/0.58    r2_hidden(sK3,k1_xboole_0) | ~spl11_26),
% 0.20/0.58    inference(superposition,[],[f86,f631])).
% 0.20/0.58  fof(f631,plain,(
% 0.20/0.58    k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) | ~spl11_26),
% 0.20/0.58    inference(avatar_component_clause,[],[f629])).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 0.20/0.58    inference(equality_resolution,[],[f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 0.20/0.58    inference(equality_resolution,[],[f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.58    inference(definition_unfolding,[],[f59,f67])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f655,plain,(
% 0.20/0.58    spl11_27),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f650])).
% 0.20/0.58  fof(f650,plain,(
% 0.20/0.58    $false | spl11_27),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f86,f635])).
% 0.20/0.58  fof(f635,plain,(
% 0.20/0.58    ~r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | spl11_27),
% 0.20/0.58    inference(avatar_component_clause,[],[f633])).
% 0.20/0.59  fof(f636,plain,(
% 0.20/0.59    spl11_26 | ~spl11_27 | ~spl11_18),
% 0.20/0.59    inference(avatar_split_clause,[],[f627,f411,f633,f629])).
% 0.20/0.59  fof(f411,plain,(
% 0.20/0.59    spl11_18 <=> sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.20/0.59  fof(f627,plain,(
% 0.20/0.59    ~r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) | ~spl11_18),
% 0.20/0.59    inference(equality_resolution,[],[f620])).
% 0.20/0.59  fof(f620,plain,(
% 0.20/0.59    ( ! [X20] : (sK3 != X20 | ~r2_hidden(sK3,k1_enumset1(X20,X20,sK3)) | k1_xboole_0 = k1_enumset1(X20,X20,sK3)) ) | ~spl11_18),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f597])).
% 0.20/0.59  fof(f597,plain,(
% 0.20/0.59    ( ! [X20] : (sK3 != X20 | ~r2_hidden(sK3,k1_enumset1(X20,X20,sK3)) | k1_xboole_0 = k1_enumset1(X20,X20,sK3) | k1_xboole_0 = k1_enumset1(X20,X20,sK3) | ~r2_hidden(sK3,k1_enumset1(X20,X20,sK3))) ) | ~spl11_18),
% 0.20/0.59    inference(superposition,[],[f415,f589])).
% 0.20/0.59  fof(f589,plain,(
% 0.20/0.59    ( ! [X0] : (sK4(k1_enumset1(X0,X0,sK3)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,sK3) | ~r2_hidden(sK3,k1_enumset1(X0,X0,sK3))) ) | ~spl11_18),
% 0.20/0.59    inference(equality_resolution,[],[f451])).
% 0.20/0.59  fof(f451,plain,(
% 0.20/0.59    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(sK3,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) = k1_xboole_0 | sK4(k1_enumset1(X0,X0,X1)) = X0) ) | ~spl11_18),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f443])).
% 0.20/0.59  fof(f443,plain,(
% 0.20/0.59    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(sK3,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) = k1_xboole_0 | sK4(k1_enumset1(X0,X0,X1)) = X0 | k1_enumset1(X0,X0,X1) = k1_xboole_0) ) | ~spl11_18),
% 0.20/0.59    inference(superposition,[],[f415,f131])).
% 0.20/0.59  fof(f415,plain,(
% 0.20/0.59    ( ! [X0] : (sK3 != sK4(X0) | ~r2_hidden(sK3,X0) | k1_xboole_0 = X0) ) | ~spl11_18),
% 0.20/0.59    inference(superposition,[],[f71,f413])).
% 0.20/0.59  fof(f413,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3)) | ~spl11_18),
% 0.20/0.59    inference(avatar_component_clause,[],[f411])).
% 0.20/0.59  fof(f71,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.20/0.59    inference(definition_unfolding,[],[f46,f48])).
% 0.20/0.59  fof(f46,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f23])).
% 0.20/0.59  fof(f414,plain,(
% 0.20/0.59    spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_18 | ~spl11_5 | ~spl11_9),
% 0.20/0.59    inference(avatar_split_clause,[],[f396,f320,f115,f411,f108,f103,f98,f93])).
% 0.20/0.59  fof(f115,plain,(
% 0.20/0.59    spl11_5 <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.20/0.59  fof(f396,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3)) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl11_5 | ~spl11_9)),
% 0.20/0.59    inference(forward_demodulation,[],[f395,f322])).
% 0.20/0.59  fof(f322,plain,(
% 0.20/0.59    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | ~spl11_9),
% 0.20/0.59    inference(avatar_component_clause,[],[f320])).
% 0.20/0.59  fof(f395,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_5),
% 0.20/0.59    inference(superposition,[],[f69,f117])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | ~spl11_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f115])).
% 0.20/0.59  fof(f373,plain,(
% 0.20/0.59    spl11_13 | ~spl11_12),
% 0.20/0.59    inference(avatar_split_clause,[],[f363,f356,f370])).
% 0.20/0.59  fof(f356,plain,(
% 0.20/0.59    spl11_12 <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_mcart_1(sK3))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.20/0.59  fof(f363,plain,(
% 0.20/0.59    k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = k1_mcart_1(sK3) | ~spl11_12),
% 0.20/0.59    inference(superposition,[],[f63,f358])).
% 0.20/0.59  fof(f358,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_mcart_1(sK3)) | ~spl11_12),
% 0.20/0.59    inference(avatar_component_clause,[],[f356])).
% 0.20/0.59  fof(f359,plain,(
% 0.20/0.59    spl11_12 | ~spl11_8 | ~spl11_9),
% 0.20/0.59    inference(avatar_split_clause,[],[f354,f320,f304,f356])).
% 0.20/0.59  fof(f304,plain,(
% 0.20/0.59    spl11_8 <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.20/0.59  fof(f354,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_mcart_1(sK3)) | (~spl11_8 | ~spl11_9)),
% 0.20/0.59    inference(forward_demodulation,[],[f306,f322])).
% 0.20/0.59  fof(f306,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl11_8),
% 0.20/0.59    inference(avatar_component_clause,[],[f304])).
% 0.20/0.59  fof(f344,plain,(
% 0.20/0.59    ~spl11_10),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f331])).
% 0.20/0.59  fof(f331,plain,(
% 0.20/0.59    $false | ~spl11_10),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f112,f329])).
% 0.20/0.59  fof(f329,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) | ~spl11_10),
% 0.20/0.59    inference(avatar_component_clause,[],[f327])).
% 0.20/0.59  fof(f327,plain,(
% 0.20/0.59    spl11_10 <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.20/0.59  fof(f330,plain,(
% 0.20/0.59    spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_10 | ~spl11_7),
% 0.20/0.59    inference(avatar_split_clause,[],[f324,f123,f327,f108,f103,f98,f93])).
% 0.20/0.59  fof(f123,plain,(
% 0.20/0.59    spl11_7 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.20/0.59  fof(f324,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_7),
% 0.20/0.59    inference(superposition,[],[f69,f125])).
% 0.20/0.59  fof(f125,plain,(
% 0.20/0.59    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | ~spl11_7),
% 0.20/0.59    inference(avatar_component_clause,[],[f123])).
% 0.20/0.59  fof(f307,plain,(
% 0.20/0.59    spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_8 | ~spl11_6),
% 0.20/0.59    inference(avatar_split_clause,[],[f255,f119,f304,f108,f103,f98,f93])).
% 0.20/0.59  fof(f119,plain,(
% 0.20/0.59    spl11_6 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.20/0.59  fof(f255,plain,(
% 0.20/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_6),
% 0.20/0.59    inference(superposition,[],[f69,f121])).
% 0.20/0.59  fof(f121,plain,(
% 0.20/0.59    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | ~spl11_6),
% 0.20/0.59    inference(avatar_component_clause,[],[f119])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    spl11_5 | spl11_6 | spl11_7),
% 0.20/0.59    inference(avatar_split_clause,[],[f39,f123,f119,f115])).
% 0.20/0.60  fof(f39,plain,(
% 0.20/0.60    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.20/0.60    inference(cnf_transformation,[],[f19])).
% 0.20/0.60  fof(f19,plain,(
% 0.20/0.60    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18,f17])).
% 0.20/0.60  fof(f17,plain,(
% 0.20/0.60    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f18,plain,(
% 0.20/0.60    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f13,plain,(
% 0.20/0.60    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.60    inference(ennf_transformation,[],[f12])).
% 0.20/0.60  fof(f12,negated_conjecture,(
% 0.20/0.60    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.60    inference(negated_conjecture,[],[f11])).
% 0.20/0.60  fof(f11,conjecture,(
% 0.20/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 0.20/0.60  fof(f111,plain,(
% 0.20/0.60    spl11_4),
% 0.20/0.60    inference(avatar_split_clause,[],[f68,f108])).
% 0.20/0.60  fof(f68,plain,(
% 0.20/0.60    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.60    inference(definition_unfolding,[],[f38,f41])).
% 0.20/0.60  fof(f38,plain,(
% 0.20/0.60    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.60    inference(cnf_transformation,[],[f19])).
% 0.20/0.60  fof(f106,plain,(
% 0.20/0.60    ~spl11_3),
% 0.20/0.60    inference(avatar_split_clause,[],[f37,f103])).
% 0.20/0.60  fof(f37,plain,(
% 0.20/0.60    k1_xboole_0 != sK2),
% 0.20/0.60    inference(cnf_transformation,[],[f19])).
% 0.20/0.60  fof(f101,plain,(
% 0.20/0.60    ~spl11_2),
% 0.20/0.60    inference(avatar_split_clause,[],[f36,f98])).
% 0.20/0.60  fof(f36,plain,(
% 0.20/0.60    k1_xboole_0 != sK1),
% 0.20/0.60    inference(cnf_transformation,[],[f19])).
% 0.20/0.60  fof(f96,plain,(
% 0.20/0.60    ~spl11_1),
% 0.20/0.60    inference(avatar_split_clause,[],[f35,f93])).
% 0.20/0.60  fof(f35,plain,(
% 0.20/0.60    k1_xboole_0 != sK0),
% 0.20/0.60    inference(cnf_transformation,[],[f19])).
% 0.20/0.60  % SZS output end Proof for theBenchmark
% 0.20/0.60  % (28423)------------------------------
% 0.20/0.60  % (28423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (28423)Termination reason: Refutation
% 0.20/0.60  
% 0.20/0.60  % (28423)Memory used [KB]: 11513
% 0.20/0.60  % (28423)Time elapsed: 0.163 s
% 0.20/0.60  % (28423)------------------------------
% 0.20/0.60  % (28423)------------------------------
% 0.20/0.60  % (28399)Success in time 0.233 s
%------------------------------------------------------------------------------
