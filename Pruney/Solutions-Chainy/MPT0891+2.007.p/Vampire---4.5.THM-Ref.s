%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:07 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 763 expanded)
%              Number of leaves         :   25 ( 256 expanded)
%              Depth                    :   18
%              Number of atoms          :  510 (3849 expanded)
%              Number of equality atoms :  340 (3005 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f465,f480,f526])).

fof(f526,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | ~ spl8_1 ),
    inference(resolution,[],[f518,f108])).

fof(f108,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f518,plain,
    ( ! [X2] : ~ r2_hidden(sK4,k1_enumset1(X2,X2,X2))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f496,f265])).

fof(f265,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X0,X3))
      | X1 = X2
      | X0 = X1
      | X1 = X3 ) ),
    inference(resolution,[],[f77,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK7(X0,X1,X2,X3) != X0
              & sK7(X0,X1,X2,X3) != X1
              & sK7(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sK7(X0,X1,X2,X3) = X0
            | sK7(X0,X1,X2,X3) = X1
            | sK7(X0,X1,X2,X3) = X2
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK7(X0,X1,X2,X3) != X0
            & sK7(X0,X1,X2,X3) != X1
            & sK7(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sK7(X0,X1,X2,X3) = X0
          | sK7(X0,X1,X2,X3) = X1
          | sK7(X0,X1,X2,X3) = X2
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f496,plain,
    ( ! [X2] :
        ( sK4 != X2
        | ~ r2_hidden(sK4,k1_enumset1(X2,X2,X2)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f178,f493])).

fof(f493,plain,
    ( sK4 = k4_tarski(k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f481,f482])).

fof(f482,plain,
    ( sK4 = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f375,f118])).

fof(f118,plain,
    ( sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_1
  <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f375,plain,(
    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f374,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
      | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
      | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f27,f26])).

fof(f26,plain,
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
          ( ( k7_mcart_1(sK1,sK2,sK3,X3) = X3
            | k6_mcart_1(sK1,sK2,sK3,X3) = X3
            | k5_mcart_1(sK1,sK2,sK3,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK1,sK2,sK3,X3) = X3
          | k6_mcart_1(sK1,sK2,sK3,X3) = X3
          | k5_mcart_1(sK1,sK2,sK3,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3)) )
   => ( ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
        | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
        | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f374,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f373,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

% (4050)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f373,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f372,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f372,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f104,f88])).

fof(f88,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f48,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f66])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f481,plain,(
    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f466,f362])).

fof(f362,plain,(
    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f361,f45])).

fof(f361,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f360,f46])).

fof(f360,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f359,f47])).

fof(f359,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f103,f88])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f75,f66])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f466,plain,(
    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f426,f375])).

fof(f426,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f425,f351])).

fof(f351,plain,(
    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f350,f45])).

fof(f350,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f349,f46])).

fof(f349,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f348,f47])).

fof(f348,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f102,f88])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f66])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f425,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f424,f45])).

fof(f424,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f423,f46])).

fof(f423,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f422,f47])).

fof(f422,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f101,f88])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f65,f66])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0)) ) ),
    inference(subsumption_resolution,[],[f177,f160])).

fof(f160,plain,(
    ! [X0,X1] : k1_xboole_0 != k1_enumset1(X0,X0,X1) ),
    inference(subsumption_resolution,[],[f159,f134])).

fof(f134,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f110,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f110,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f68,f87])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f159,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_enumset1(X0,X0,X1)
      | r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f99,f51])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f71,f58])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f90,f168])).

fof(f168,plain,(
    ! [X1] : sK5(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(subsumption_resolution,[],[f150,f160])).

fof(f150,plain,(
    ! [X1] :
      ( sK5(k1_enumset1(X1,X1,X1)) = X1
      | k1_xboole_0 = k1_enumset1(X1,X1,X1) ) ),
    inference(resolution,[],[f109,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f109,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f87])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f56,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f480,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f478,f132])).

fof(f132,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f105,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f105,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f478,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),sK4)
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f466,f471])).

fof(f471,plain,
    ( sK4 = k2_mcart_1(sK4)
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f351,f126])).

fof(f126,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_3
  <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f465,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | ~ spl8_2 ),
    inference(resolution,[],[f453,f108])).

fof(f453,plain,
    ( ! [X4] : ~ r2_hidden(sK4,k1_enumset1(X4,X4,X4))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f433,f265])).

fof(f433,plain,
    ( ! [X4] :
        ( sK4 != X4
        | ~ r2_hidden(sK4,k1_enumset1(X4,X4,X4)) )
    | ~ spl8_2 ),
    inference(superposition,[],[f171,f428])).

fof(f428,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f427,f375])).

fof(f427,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k2_mcart_1(sK4))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f426,f122])).

fof(f122,plain,
    ( sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_2
  <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X2,k1_enumset1(X0,X0,X0)) ) ),
    inference(subsumption_resolution,[],[f169,f160])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f89,f168])).

fof(f89,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f57,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f127,plain,
    ( spl8_1
    | spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f49,f124,f120,f116])).

fof(f49,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (4049)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (4061)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (4055)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (4041)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (4043)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (4069)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (4064)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (4046)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (4045)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (4044)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (4056)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (4047)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  % (4065)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.54  % (4067)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (4068)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.54  % (4055)Refutation not found, incomplete strategy% (4055)------------------------------
% 1.33/0.54  % (4055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (4055)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (4055)Memory used [KB]: 1791
% 1.33/0.54  % (4055)Time elapsed: 0.124 s
% 1.33/0.54  % (4055)------------------------------
% 1.33/0.54  % (4055)------------------------------
% 1.33/0.54  % (4067)Refutation not found, incomplete strategy% (4067)------------------------------
% 1.33/0.54  % (4067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (4067)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (4067)Memory used [KB]: 6268
% 1.33/0.54  % (4067)Time elapsed: 0.139 s
% 1.33/0.54  % (4067)------------------------------
% 1.33/0.54  % (4067)------------------------------
% 1.33/0.55  % (4048)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.55  % (4068)Refutation not found, incomplete strategy% (4068)------------------------------
% 1.33/0.55  % (4068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (4057)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.55  % (4058)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.55  % (4060)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.55  % (4053)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.55  % (4051)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.33/0.55  % (4053)Refutation not found, incomplete strategy% (4053)------------------------------
% 1.33/0.55  % (4053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (4053)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (4053)Memory used [KB]: 10746
% 1.33/0.55  % (4053)Time elapsed: 0.139 s
% 1.33/0.55  % (4053)------------------------------
% 1.33/0.55  % (4053)------------------------------
% 1.33/0.55  % (4052)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.55  % (4070)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.55  % (4057)Refutation not found, incomplete strategy% (4057)------------------------------
% 1.33/0.55  % (4057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (4066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.55  % (4059)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.56  % (4054)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.56  % (4069)Refutation not found, incomplete strategy% (4069)------------------------------
% 1.33/0.56  % (4069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (4063)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.53/0.56  % (4065)Refutation not found, incomplete strategy% (4065)------------------------------
% 1.53/0.56  % (4065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (4058)Refutation not found, incomplete strategy% (4058)------------------------------
% 1.53/0.56  % (4058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (4059)Refutation not found, incomplete strategy% (4059)------------------------------
% 1.53/0.56  % (4059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (4068)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (4068)Memory used [KB]: 6268
% 1.53/0.56  % (4068)Time elapsed: 0.141 s
% 1.53/0.56  % (4068)------------------------------
% 1.53/0.56  % (4068)------------------------------
% 1.53/0.56  % (4059)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (4059)Memory used [KB]: 1791
% 1.53/0.56  % (4059)Time elapsed: 0.146 s
% 1.53/0.56  % (4059)------------------------------
% 1.53/0.56  % (4059)------------------------------
% 1.53/0.56  % (4069)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (4069)Memory used [KB]: 11001
% 1.53/0.56  % (4069)Time elapsed: 0.136 s
% 1.53/0.56  % (4069)------------------------------
% 1.53/0.56  % (4069)------------------------------
% 1.53/0.57  % (4070)Refutation not found, incomplete strategy% (4070)------------------------------
% 1.53/0.57  % (4070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (4070)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (4070)Memory used [KB]: 1663
% 1.53/0.57  % (4070)Time elapsed: 0.004 s
% 1.53/0.57  % (4070)------------------------------
% 1.53/0.57  % (4070)------------------------------
% 1.53/0.57  % (4042)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.53/0.57  % (4057)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (4057)Memory used [KB]: 10746
% 1.53/0.57  % (4057)Time elapsed: 0.138 s
% 1.53/0.57  % (4057)------------------------------
% 1.53/0.57  % (4057)------------------------------
% 1.53/0.57  % (4065)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (4065)Memory used [KB]: 10746
% 1.53/0.57  % (4065)Time elapsed: 0.149 s
% 1.53/0.57  % (4065)------------------------------
% 1.53/0.57  % (4065)------------------------------
% 1.53/0.57  % (4047)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % (4058)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (4058)Memory used [KB]: 1791
% 1.53/0.57  % (4058)Time elapsed: 0.150 s
% 1.53/0.57  % (4058)------------------------------
% 1.53/0.57  % (4058)------------------------------
% 1.53/0.59  % SZS output start Proof for theBenchmark
% 1.53/0.59  fof(f527,plain,(
% 1.53/0.59    $false),
% 1.53/0.59    inference(avatar_sat_refutation,[],[f127,f465,f480,f526])).
% 1.53/0.59  fof(f526,plain,(
% 1.53/0.59    ~spl8_1),
% 1.53/0.59    inference(avatar_contradiction_clause,[],[f519])).
% 1.53/0.59  fof(f519,plain,(
% 1.53/0.59    $false | ~spl8_1),
% 1.53/0.59    inference(resolution,[],[f518,f108])).
% 1.53/0.59  fof(f108,plain,(
% 1.53/0.59    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 1.53/0.59    inference(equality_resolution,[],[f107])).
% 1.53/0.59  fof(f107,plain,(
% 1.53/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 1.53/0.59    inference(equality_resolution,[],[f93])).
% 1.53/0.59  fof(f93,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 1.53/0.59    inference(definition_unfolding,[],[f62,f87])).
% 1.53/0.59  fof(f87,plain,(
% 1.53/0.59    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f52,f58])).
% 1.53/0.59  fof(f58,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f6])).
% 1.53/0.59  fof(f6,axiom,(
% 1.53/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.59  fof(f52,plain,(
% 1.53/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f5])).
% 1.53/0.59  fof(f5,axiom,(
% 1.53/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.59  fof(f62,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.53/0.59    inference(cnf_transformation,[],[f34])).
% 1.53/0.59  fof(f34,plain,(
% 1.53/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.53/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 1.53/0.59  fof(f33,plain,(
% 1.53/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f32,plain,(
% 1.53/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.53/0.59    inference(rectify,[],[f31])).
% 1.53/0.59  fof(f31,plain,(
% 1.53/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.53/0.59    inference(nnf_transformation,[],[f4])).
% 1.53/0.59  fof(f4,axiom,(
% 1.53/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.53/0.59  fof(f518,plain,(
% 1.53/0.59    ( ! [X2] : (~r2_hidden(sK4,k1_enumset1(X2,X2,X2))) ) | ~spl8_1),
% 1.53/0.59    inference(subsumption_resolution,[],[f496,f265])).
% 1.53/0.59  fof(f265,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k1_enumset1(X2,X0,X3)) | X1 = X2 | X0 = X1 | X1 = X3) )),
% 1.53/0.59    inference(resolution,[],[f77,f114])).
% 1.53/0.59  fof(f114,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.53/0.59    inference(equality_resolution,[],[f85])).
% 1.53/0.59  fof(f85,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.53/0.59    inference(cnf_transformation,[],[f44])).
% 1.53/0.59  fof(f44,plain,(
% 1.53/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.53/0.59    inference(nnf_transformation,[],[f25])).
% 1.53/0.59  fof(f25,plain,(
% 1.53/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.53/0.59    inference(definition_folding,[],[f23,f24])).
% 1.53/0.59  fof(f24,plain,(
% 1.53/0.59    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.53/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.53/0.59  fof(f23,plain,(
% 1.53/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.53/0.59    inference(ennf_transformation,[],[f3])).
% 1.53/0.59  fof(f3,axiom,(
% 1.53/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.53/0.59  fof(f77,plain,(
% 1.53/0.59    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 1.53/0.59    inference(cnf_transformation,[],[f43])).
% 1.53/0.59  fof(f43,plain,(
% 1.53/0.59    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.53/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).
% 1.53/0.59  fof(f42,plain,(
% 1.53/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f41,plain,(
% 1.53/0.59    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.53/0.59    inference(rectify,[],[f40])).
% 1.53/0.59  fof(f40,plain,(
% 1.53/0.59    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.53/0.59    inference(flattening,[],[f39])).
% 1.53/0.59  fof(f39,plain,(
% 1.53/0.59    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.53/0.59    inference(nnf_transformation,[],[f24])).
% 1.53/0.59  fof(f496,plain,(
% 1.53/0.59    ( ! [X2] : (sK4 != X2 | ~r2_hidden(sK4,k1_enumset1(X2,X2,X2))) ) | ~spl8_1),
% 1.53/0.59    inference(superposition,[],[f178,f493])).
% 1.53/0.59  fof(f493,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) | ~spl8_1),
% 1.53/0.59    inference(forward_demodulation,[],[f481,f482])).
% 1.53/0.59  fof(f482,plain,(
% 1.53/0.59    sK4 = k1_mcart_1(k1_mcart_1(sK4)) | ~spl8_1),
% 1.53/0.59    inference(backward_demodulation,[],[f375,f118])).
% 1.53/0.59  fof(f118,plain,(
% 1.53/0.59    sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) | ~spl8_1),
% 1.53/0.59    inference(avatar_component_clause,[],[f116])).
% 1.53/0.59  fof(f116,plain,(
% 1.53/0.59    spl8_1 <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.53/0.59  fof(f375,plain,(
% 1.53/0.59    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 1.53/0.59    inference(subsumption_resolution,[],[f374,f45])).
% 1.53/0.59  fof(f45,plain,(
% 1.53/0.59    k1_xboole_0 != sK1),
% 1.53/0.59    inference(cnf_transformation,[],[f28])).
% 1.53/0.59  fof(f28,plain,(
% 1.53/0.59    ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1),
% 1.53/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f27,f26])).
% 1.53/0.59  fof(f26,plain,(
% 1.53/0.59    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1)),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f27,plain,(
% 1.53/0.59    ? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) => ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f18,plain,(
% 1.53/0.59    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.53/0.59    inference(ennf_transformation,[],[f17])).
% 1.53/0.59  fof(f17,negated_conjecture,(
% 1.53/0.59    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.53/0.59    inference(negated_conjecture,[],[f16])).
% 1.53/0.59  fof(f16,conjecture,(
% 1.53/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.53/0.59  fof(f374,plain,(
% 1.53/0.59    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1),
% 1.53/0.59    inference(subsumption_resolution,[],[f373,f46])).
% 1.53/0.59  fof(f46,plain,(
% 1.53/0.59    k1_xboole_0 != sK2),
% 1.53/0.59    inference(cnf_transformation,[],[f28])).
% 1.53/0.59  % (4050)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.53/0.59  fof(f373,plain,(
% 1.53/0.59    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.53/0.59    inference(subsumption_resolution,[],[f372,f47])).
% 1.53/0.59  fof(f47,plain,(
% 1.53/0.59    k1_xboole_0 != sK3),
% 1.53/0.59    inference(cnf_transformation,[],[f28])).
% 1.53/0.59  fof(f372,plain,(
% 1.53/0.59    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.53/0.59    inference(resolution,[],[f104,f88])).
% 1.53/0.59  fof(f88,plain,(
% 1.53/0.59    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.53/0.59    inference(definition_unfolding,[],[f48,f66])).
% 1.53/0.59  fof(f66,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f10])).
% 1.53/0.59  fof(f10,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.53/0.59  fof(f48,plain,(
% 1.53/0.59    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))),
% 1.53/0.59    inference(cnf_transformation,[],[f28])).
% 1.53/0.59  fof(f104,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(definition_unfolding,[],[f74,f66])).
% 1.53/0.59  fof(f74,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f22])).
% 1.53/0.59  fof(f22,plain,(
% 1.53/0.59    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.53/0.59    inference(ennf_transformation,[],[f14])).
% 1.53/0.59  fof(f14,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.53/0.59  fof(f481,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))),
% 1.53/0.59    inference(forward_demodulation,[],[f466,f362])).
% 1.53/0.59  fof(f362,plain,(
% 1.53/0.59    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.53/0.59    inference(subsumption_resolution,[],[f361,f45])).
% 1.53/0.59  fof(f361,plain,(
% 1.53/0.59    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1),
% 1.53/0.59    inference(subsumption_resolution,[],[f360,f46])).
% 1.53/0.59  fof(f360,plain,(
% 1.53/0.59    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.53/0.59    inference(subsumption_resolution,[],[f359,f47])).
% 1.53/0.59  fof(f359,plain,(
% 1.53/0.59    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.53/0.59    inference(resolution,[],[f103,f88])).
% 1.53/0.59  fof(f103,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(definition_unfolding,[],[f75,f66])).
% 1.53/0.59  fof(f75,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f22])).
% 1.53/0.59  fof(f466,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 1.53/0.59    inference(forward_demodulation,[],[f426,f375])).
% 1.53/0.59  fof(f426,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 1.53/0.59    inference(forward_demodulation,[],[f425,f351])).
% 1.53/0.59  fof(f351,plain,(
% 1.53/0.59    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 1.53/0.59    inference(subsumption_resolution,[],[f350,f45])).
% 1.53/0.59  fof(f350,plain,(
% 1.53/0.59    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1),
% 1.53/0.59    inference(subsumption_resolution,[],[f349,f46])).
% 1.53/0.59  fof(f349,plain,(
% 1.53/0.59    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.53/0.59    inference(subsumption_resolution,[],[f348,f47])).
% 1.53/0.59  fof(f348,plain,(
% 1.53/0.59    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.53/0.59    inference(resolution,[],[f102,f88])).
% 1.53/0.59  fof(f102,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(definition_unfolding,[],[f76,f66])).
% 1.53/0.59  fof(f76,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f22])).
% 1.53/0.59  fof(f425,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))),
% 1.53/0.59    inference(subsumption_resolution,[],[f424,f45])).
% 1.53/0.59  fof(f424,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK1),
% 1.53/0.59    inference(subsumption_resolution,[],[f423,f46])).
% 1.53/0.59  fof(f423,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.53/0.59    inference(subsumption_resolution,[],[f422,f47])).
% 1.53/0.59  fof(f422,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.53/0.59    inference(resolution,[],[f101,f88])).
% 1.53/0.59  fof(f101,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(definition_unfolding,[],[f73,f65,f66])).
% 1.53/0.59  fof(f65,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f9])).
% 1.53/0.59  fof(f9,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.53/0.59  fof(f73,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f21])).
% 1.53/0.59  fof(f21,plain,(
% 1.53/0.59    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.53/0.59    inference(ennf_transformation,[],[f13])).
% 1.53/0.59  fof(f13,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.53/0.59  fof(f178,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X0))) )),
% 1.53/0.59    inference(subsumption_resolution,[],[f177,f160])).
% 1.53/0.59  fof(f160,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k1_xboole_0 != k1_enumset1(X0,X0,X1)) )),
% 1.53/0.59    inference(subsumption_resolution,[],[f159,f134])).
% 1.53/0.59  fof(f134,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.53/0.59    inference(superposition,[],[f110,f50])).
% 1.53/0.59  fof(f50,plain,(
% 1.53/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f2])).
% 1.53/0.59  fof(f2,axiom,(
% 1.53/0.59    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.53/0.59  fof(f110,plain,(
% 1.53/0.59    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.53/0.59    inference(equality_resolution,[],[f96])).
% 1.53/0.59  fof(f96,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.53/0.59    inference(definition_unfolding,[],[f68,f87])).
% 1.53/0.59  fof(f68,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f36])).
% 1.53/0.59  fof(f36,plain,(
% 1.53/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.53/0.59    inference(flattening,[],[f35])).
% 1.53/0.59  fof(f35,plain,(
% 1.53/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.53/0.59    inference(nnf_transformation,[],[f7])).
% 1.53/0.59  fof(f7,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.53/0.59  fof(f159,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k1_xboole_0 != k1_enumset1(X0,X0,X1) | r2_hidden(X1,k1_xboole_0)) )),
% 1.53/0.59    inference(superposition,[],[f99,f51])).
% 1.53/0.59  fof(f51,plain,(
% 1.53/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f1])).
% 1.53/0.59  fof(f1,axiom,(
% 1.53/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.53/0.59  fof(f99,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f71,f58])).
% 1.53/0.59  fof(f71,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f38])).
% 1.53/0.59  fof(f38,plain,(
% 1.53/0.59    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.53/0.59    inference(flattening,[],[f37])).
% 1.53/0.59  fof(f37,plain,(
% 1.53/0.59    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.53/0.59    inference(nnf_transformation,[],[f8])).
% 1.53/0.59  fof(f8,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.53/0.59  fof(f177,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.53/0.59    inference(superposition,[],[f90,f168])).
% 1.53/0.59  fof(f168,plain,(
% 1.53/0.59    ( ! [X1] : (sK5(k1_enumset1(X1,X1,X1)) = X1) )),
% 1.53/0.59    inference(subsumption_resolution,[],[f150,f160])).
% 1.53/0.59  fof(f150,plain,(
% 1.53/0.59    ( ! [X1] : (sK5(k1_enumset1(X1,X1,X1)) = X1 | k1_xboole_0 = k1_enumset1(X1,X1,X1)) )),
% 1.53/0.59    inference(resolution,[],[f109,f55])).
% 1.53/0.59  fof(f55,plain,(
% 1.53/0.59    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f30])).
% 1.53/0.59  fof(f30,plain,(
% 1.53/0.59    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 1.53/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f29])).
% 1.53/0.59  fof(f29,plain,(
% 1.53/0.59    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f20,plain,(
% 1.53/0.59    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.53/0.59    inference(ennf_transformation,[],[f12])).
% 1.53/0.59  fof(f12,axiom,(
% 1.53/0.59    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.53/0.59  fof(f109,plain,(
% 1.53/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 1.53/0.59    inference(equality_resolution,[],[f94])).
% 1.53/0.59  fof(f94,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.53/0.59    inference(definition_unfolding,[],[f61,f87])).
% 1.53/0.59  fof(f61,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.53/0.59    inference(cnf_transformation,[],[f34])).
% 1.53/0.59  fof(f90,plain,(
% 1.53/0.59    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(definition_unfolding,[],[f56,f65])).
% 1.53/0.59  fof(f56,plain,(
% 1.53/0.59    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f30])).
% 1.53/0.59  fof(f480,plain,(
% 1.53/0.59    ~spl8_3),
% 1.53/0.59    inference(avatar_contradiction_clause,[],[f479])).
% 1.53/0.59  fof(f479,plain,(
% 1.53/0.59    $false | ~spl8_3),
% 1.53/0.59    inference(subsumption_resolution,[],[f478,f132])).
% 1.53/0.59  fof(f132,plain,(
% 1.53/0.59    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.53/0.59    inference(forward_demodulation,[],[f105,f60])).
% 1.53/0.59  fof(f60,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.53/0.59    inference(cnf_transformation,[],[f15])).
% 1.53/0.59  fof(f15,axiom,(
% 1.53/0.59    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.53/0.59  fof(f105,plain,(
% 1.53/0.59    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.53/0.59    inference(equality_resolution,[],[f54])).
% 1.53/0.59  fof(f54,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f19])).
% 1.53/0.59  fof(f19,plain,(
% 1.53/0.59    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.53/0.59    inference(ennf_transformation,[],[f11])).
% 1.53/0.59  fof(f11,axiom,(
% 1.53/0.59    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.53/0.59  fof(f478,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),sK4) | ~spl8_3),
% 1.53/0.59    inference(forward_demodulation,[],[f466,f471])).
% 1.53/0.59  fof(f471,plain,(
% 1.53/0.59    sK4 = k2_mcart_1(sK4) | ~spl8_3),
% 1.53/0.59    inference(backward_demodulation,[],[f351,f126])).
% 1.53/0.59  fof(f126,plain,(
% 1.53/0.59    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | ~spl8_3),
% 1.53/0.59    inference(avatar_component_clause,[],[f124])).
% 1.53/0.59  fof(f124,plain,(
% 1.53/0.59    spl8_3 <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.53/0.59  fof(f465,plain,(
% 1.53/0.59    ~spl8_2),
% 1.53/0.59    inference(avatar_contradiction_clause,[],[f458])).
% 1.53/0.59  fof(f458,plain,(
% 1.53/0.59    $false | ~spl8_2),
% 1.53/0.59    inference(resolution,[],[f453,f108])).
% 1.53/0.59  fof(f453,plain,(
% 1.53/0.59    ( ! [X4] : (~r2_hidden(sK4,k1_enumset1(X4,X4,X4))) ) | ~spl8_2),
% 1.53/0.59    inference(subsumption_resolution,[],[f433,f265])).
% 1.53/0.59  fof(f433,plain,(
% 1.53/0.59    ( ! [X4] : (sK4 != X4 | ~r2_hidden(sK4,k1_enumset1(X4,X4,X4))) ) | ~spl8_2),
% 1.53/0.59    inference(superposition,[],[f171,f428])).
% 1.53/0.59  fof(f428,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4)) | ~spl8_2),
% 1.53/0.59    inference(forward_demodulation,[],[f427,f375])).
% 1.53/0.59  fof(f427,plain,(
% 1.53/0.59    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k2_mcart_1(sK4)) | ~spl8_2),
% 1.53/0.59    inference(forward_demodulation,[],[f426,f122])).
% 1.53/0.59  fof(f122,plain,(
% 1.53/0.59    sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | ~spl8_2),
% 1.53/0.59    inference(avatar_component_clause,[],[f120])).
% 1.53/0.59  fof(f120,plain,(
% 1.53/0.59    spl8_2 <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.53/0.59  fof(f171,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X2,k1_enumset1(X0,X0,X0))) )),
% 1.53/0.59    inference(subsumption_resolution,[],[f169,f160])).
% 1.53/0.59  fof(f169,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.53/0.59    inference(superposition,[],[f89,f168])).
% 1.53/0.59  fof(f89,plain,(
% 1.53/0.59    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(definition_unfolding,[],[f57,f65])).
% 1.53/0.59  fof(f57,plain,(
% 1.53/0.59    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f30])).
% 1.53/0.59  fof(f127,plain,(
% 1.53/0.59    spl8_1 | spl8_2 | spl8_3),
% 1.53/0.59    inference(avatar_split_clause,[],[f49,f124,f120,f116])).
% 1.53/0.59  fof(f49,plain,(
% 1.53/0.59    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.53/0.59    inference(cnf_transformation,[],[f28])).
% 1.53/0.59  % SZS output end Proof for theBenchmark
% 1.53/0.59  % (4047)------------------------------
% 1.53/0.59  % (4047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (4047)Termination reason: Refutation
% 1.53/0.59  
% 1.53/0.59  % (4047)Memory used [KB]: 11129
% 1.53/0.59  % (4047)Time elapsed: 0.165 s
% 1.53/0.59  % (4047)------------------------------
% 1.53/0.59  % (4047)------------------------------
% 1.53/0.60  % (4040)Success in time 0.232 s
%------------------------------------------------------------------------------
