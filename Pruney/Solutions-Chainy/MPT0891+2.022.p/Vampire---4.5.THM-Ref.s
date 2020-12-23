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
% DateTime   : Thu Dec  3 12:59:09 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 681 expanded)
%              Number of leaves         :   20 ( 197 expanded)
%              Depth                    :   21
%              Number of atoms          :  454 (3757 expanded)
%              Number of equality atoms :  213 (1643 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f463,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f417,f440,f461])).

fof(f461,plain,(
    ~ spl10_1 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f442,f100])).

fof(f100,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f82,f84])).

fof(f84,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f82,plain,(
    ! [X4,X2,X1] :
      ( ~ sP1(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK9(X0,X1,X2) != X0
              & sK9(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sK9(X0,X1,X2) = X0
            | sK9(X0,X1,X2) = X1
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK9(X0,X1,X2) != X0
            & sK9(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sK9(X0,X1,X2) = X0
          | sK9(X0,X1,X2) = X1
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f442,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
    | ~ spl10_1 ),
    inference(superposition,[],[f221,f441])).

fof(f441,plain,
    ( sK5 = k4_tarski(k4_tarski(sK5,k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f396,f88])).

fof(f88,plain,
    ( sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_1
  <=> sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f396,plain,(
    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f395,f42])).

fof(f42,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
      | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
      | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) )
    & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f21,f20])).

fof(f20,plain,
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
          ( ( k7_mcart_1(sK2,sK3,sK4,X3) = X3
            | k6_mcart_1(sK2,sK3,sK4,X3) = X3
            | k5_mcart_1(sK2,sK3,sK4,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4)) )
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK2,sK3,sK4,X3) = X3
          | k6_mcart_1(sK2,sK3,sK4,X3) = X3
          | k5_mcart_1(sK2,sK3,sK4,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4)) )
   => ( ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
        | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
        | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) )
      & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f395,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f394,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f394,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f393,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f393,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f80,f77])).

fof(f77,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f45,plain,(
    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f56,f55])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f221,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k2_tarski(k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2))) ),
    inference(equality_resolution,[],[f218])).

fof(f218,plain,(
    ! [X12,X10,X13,X11] :
      ( k4_tarski(k4_tarski(X11,X12),X13) != X10
      | ~ r2_hidden(X11,k2_tarski(X10,X10)) ) ),
    inference(subsumption_resolution,[],[f215,f137])).

fof(f137,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) != k1_xboole_0 ),
    inference(subsumption_resolution,[],[f136,f101])).

fof(f101,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f83,f84])).

fof(f83,plain,(
    ! [X4,X2,X0] :
      ( ~ sP1(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) != k1_xboole_0
      | ~ r2_hidden(X0,k2_tarski(X0,X1)) ) ),
    inference(superposition,[],[f73,f118])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f109,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f104,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK8(X0,X1,X2),X0)
              & r2_hidden(sK8(X0,X1,X2),X1) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK8(X0,X1,X2),X0)
            & r2_hidden(sK8(X0,X1,X2),X1) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f108,f47])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f58,f81])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f215,plain,(
    ! [X12,X10,X13,X11] :
      ( k4_tarski(k4_tarski(X11,X12),X13) != X10
      | ~ r2_hidden(X11,k2_tarski(X10,X10))
      | k1_xboole_0 = k2_tarski(X10,X10) ) ),
    inference(superposition,[],[f79,f209])).

fof(f209,plain,(
    ! [X0] : sK7(k2_tarski(X0,X0)) = X0 ),
    inference(equality_resolution,[],[f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | sK7(k2_tarski(X0,X1)) = X1 ) ),
    inference(equality_factoring,[],[f173])).

fof(f173,plain,(
    ! [X10,X9] :
      ( sK7(k2_tarski(X9,X10)) = X9
      | sK7(k2_tarski(X9,X10)) = X10 ) ),
    inference(subsumption_resolution,[],[f169,f137])).

fof(f169,plain,(
    ! [X10,X9] :
      ( sK7(k2_tarski(X9,X10)) = X9
      | sK7(k2_tarski(X9,X10)) = X10
      | k1_xboole_0 = k2_tarski(X9,X10) ) ),
    inference(resolution,[],[f164,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f14,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f65,f84])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X4,X2,X0,X3] :
      ( sK7(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f51,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK7(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f440,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f432,f100])).

fof(f432,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
    | ~ spl10_3 ),
    inference(superposition,[],[f195,f419])).

fof(f419,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),sK5)
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f396,f96])).

fof(f96,plain,
    ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl10_3
  <=> sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f195,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_tarski(k4_tarski(X1,X0),k4_tarski(X1,X0))) ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,(
    ! [X4,X2,X3] :
      ( k4_tarski(X3,X4) != X2
      | ~ r2_hidden(X4,k2_tarski(X2,X2)) ) ),
    inference(subsumption_resolution,[],[f189,f137])).

fof(f189,plain,(
    ! [X4,X2,X3] :
      ( k4_tarski(X3,X4) != X2
      | ~ r2_hidden(X4,k2_tarski(X2,X2))
      | k1_xboole_0 = k2_tarski(X2,X2) ) ),
    inference(superposition,[],[f49,f188])).

fof(f188,plain,(
    ! [X0] : sK6(k2_tarski(X0,X0)) = X0 ),
    inference(equality_resolution,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | sK6(k2_tarski(X0,X1)) = X1 ) ),
    inference(equality_factoring,[],[f172])).

fof(f172,plain,(
    ! [X4,X5] :
      ( sK6(k2_tarski(X4,X5)) = X4
      | sK6(k2_tarski(X4,X5)) = X5 ) ),
    inference(subsumption_resolution,[],[f167,f137])).

fof(f167,plain,(
    ! [X4,X5] :
      ( sK6(k2_tarski(X4,X5)) = X4
      | sK6(k2_tarski(X4,X5)) = X5
      | k1_xboole_0 = k2_tarski(X4,X5) ) ),
    inference(resolution,[],[f164,f47])).

fof(f49,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK6(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f417,plain,(
    ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f399,f100])).

fof(f399,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
    | ~ spl10_2 ),
    inference(superposition,[],[f220,f397])).

fof(f397,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),sK5),k7_mcart_1(sK2,sK3,sK4,sK5))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f396,f92])).

fof(f92,plain,
    ( sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl10_2
  <=> sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f220,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k2_tarski(k4_tarski(k4_tarski(X1,X0),X2),k4_tarski(k4_tarski(X1,X0),X2))) ),
    inference(equality_resolution,[],[f212])).

fof(f212,plain,(
    ! [X4,X2,X5,X3] :
      ( k4_tarski(k4_tarski(X3,X4),X5) != X2
      | ~ r2_hidden(X4,k2_tarski(X2,X2)) ) ),
    inference(subsumption_resolution,[],[f210,f137])).

fof(f210,plain,(
    ! [X4,X2,X5,X3] :
      ( k4_tarski(k4_tarski(X3,X4),X5) != X2
      | ~ r2_hidden(X4,k2_tarski(X2,X2))
      | k1_xboole_0 = k2_tarski(X2,X2) ) ),
    inference(superposition,[],[f78,f209])).

fof(f78,plain,(
    ! [X4,X2,X0,X3] :
      ( sK7(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f52,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK7(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,
    ( spl10_1
    | spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f46,f94,f90,f86])).

fof(f46,plain,
    ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
    | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
    | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (4973)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (4983)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (4983)Refutation not found, incomplete strategy% (4983)------------------------------
% 0.21/0.51  % (4983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4983)Memory used [KB]: 1791
% 0.21/0.51  % (4983)Time elapsed: 0.086 s
% 0.21/0.51  % (4983)------------------------------
% 0.21/0.51  % (4983)------------------------------
% 0.21/0.51  % (4970)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (4991)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.52  % (4971)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.52  % (4968)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.53  % (4986)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.54  % (4994)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.22/0.54  % (4975)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.54  % (4967)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.42/0.54  % (4978)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.42/0.54  % (4990)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.54  % (4989)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.54  % (4967)Refutation not found, incomplete strategy% (4967)------------------------------
% 1.42/0.54  % (4967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (4967)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (4967)Memory used [KB]: 1663
% 1.42/0.54  % (4967)Time elapsed: 0.125 s
% 1.42/0.54  % (4967)------------------------------
% 1.42/0.54  % (4967)------------------------------
% 1.42/0.54  % (4978)Refutation not found, incomplete strategy% (4978)------------------------------
% 1.42/0.54  % (4978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (4978)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (4978)Memory used [KB]: 10618
% 1.42/0.54  % (4978)Time elapsed: 0.127 s
% 1.42/0.54  % (4978)------------------------------
% 1.42/0.54  % (4978)------------------------------
% 1.42/0.54  % (4972)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.54  % (4990)Refutation not found, incomplete strategy% (4990)------------------------------
% 1.42/0.54  % (4990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (4990)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (4990)Memory used [KB]: 10746
% 1.42/0.54  % (4990)Time elapsed: 0.127 s
% 1.42/0.54  % (4990)------------------------------
% 1.42/0.54  % (4990)------------------------------
% 1.42/0.55  % (4969)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.42/0.55  % (4993)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.55  % (4993)Refutation not found, incomplete strategy% (4993)------------------------------
% 1.42/0.55  % (4993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (4993)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (4993)Memory used [KB]: 6268
% 1.42/0.55  % (4993)Time elapsed: 0.127 s
% 1.42/0.55  % (4993)------------------------------
% 1.42/0.55  % (4993)------------------------------
% 1.42/0.55  % (4980)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.42/0.55  % (4966)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.55  % (4980)Refutation not found, incomplete strategy% (4980)------------------------------
% 1.42/0.55  % (4980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (4980)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (4980)Memory used [KB]: 1791
% 1.42/0.55  % (4980)Time elapsed: 0.107 s
% 1.42/0.55  % (4980)------------------------------
% 1.42/0.55  % (4980)------------------------------
% 1.42/0.55  % (4985)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.55  % (4995)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (4988)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.55  % (4987)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.55  % (4995)Refutation not found, incomplete strategy% (4995)------------------------------
% 1.42/0.55  % (4995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (4995)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (4995)Memory used [KB]: 1663
% 1.42/0.55  % (4995)Time elapsed: 0.141 s
% 1.42/0.55  % (4995)------------------------------
% 1.42/0.55  % (4995)------------------------------
% 1.42/0.55  % (4981)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.55  % (4982)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.56  % (4982)Refutation not found, incomplete strategy% (4982)------------------------------
% 1.42/0.56  % (4982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (4982)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (4982)Memory used [KB]: 10618
% 1.42/0.56  % (4982)Time elapsed: 0.138 s
% 1.42/0.56  % (4982)------------------------------
% 1.42/0.56  % (4982)------------------------------
% 1.42/0.56  % (4979)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.42/0.56  % (4977)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.56  % (4974)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.56  % (4976)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.56  % (4992)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.57  % (4992)Refutation not found, incomplete strategy% (4992)------------------------------
% 1.42/0.57  % (4992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (4992)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (4992)Memory used [KB]: 6268
% 1.42/0.57  % (4992)Time elapsed: 0.145 s
% 1.42/0.57  % (4992)------------------------------
% 1.42/0.57  % (4992)------------------------------
% 1.42/0.57  % (4984)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.57  % (4984)Refutation not found, incomplete strategy% (4984)------------------------------
% 1.42/0.57  % (4984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (4984)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (4984)Memory used [KB]: 1791
% 1.42/0.57  % (4984)Time elapsed: 0.156 s
% 1.42/0.57  % (4984)------------------------------
% 1.42/0.57  % (4984)------------------------------
% 1.42/0.58  % (4972)Refutation found. Thanks to Tanya!
% 1.42/0.58  % SZS status Theorem for theBenchmark
% 1.42/0.58  % SZS output start Proof for theBenchmark
% 1.42/0.58  fof(f463,plain,(
% 1.42/0.58    $false),
% 1.42/0.58    inference(avatar_sat_refutation,[],[f97,f417,f440,f461])).
% 1.42/0.58  fof(f461,plain,(
% 1.42/0.58    ~spl10_1),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f460])).
% 1.42/0.58  fof(f460,plain,(
% 1.42/0.58    $false | ~spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f442,f100])).
% 1.42/0.58  fof(f100,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 1.42/0.58    inference(resolution,[],[f82,f84])).
% 1.42/0.58  fof(f84,plain,(
% 1.42/0.58    ( ! [X0,X1] : (sP1(X1,X0,k2_tarski(X0,X1))) )),
% 1.42/0.58    inference(equality_resolution,[],[f71])).
% 1.42/0.58  fof(f71,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.42/0.58    inference(cnf_transformation,[],[f39])).
% 1.42/0.58  fof(f39,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.42/0.58    inference(nnf_transformation,[],[f19])).
% 1.42/0.58  fof(f19,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.42/0.58    inference(definition_folding,[],[f2,f18])).
% 1.42/0.58  fof(f18,plain,(
% 1.42/0.58    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.42/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.42/0.58  fof(f2,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.42/0.58  fof(f82,plain,(
% 1.42/0.58    ( ! [X4,X2,X1] : (~sP1(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.42/0.58    inference(equality_resolution,[],[f67])).
% 1.42/0.58  fof(f67,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP1(X0,X1,X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f38])).
% 1.42/0.58  fof(f38,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK9(X0,X1,X2) != X0 & sK9(X0,X1,X2) != X1) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sK9(X0,X1,X2) = X0 | sK9(X0,X1,X2) = X1 | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.42/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).
% 1.42/0.58  fof(f37,plain,(
% 1.42/0.58    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK9(X0,X1,X2) != X0 & sK9(X0,X1,X2) != X1) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sK9(X0,X1,X2) = X0 | sK9(X0,X1,X2) = X1 | r2_hidden(sK9(X0,X1,X2),X2))))),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f36,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.42/0.58    inference(rectify,[],[f35])).
% 1.42/0.58  fof(f35,plain,(
% 1.42/0.58    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.42/0.58    inference(flattening,[],[f34])).
% 1.42/0.58  fof(f34,plain,(
% 1.42/0.58    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.42/0.58    inference(nnf_transformation,[],[f18])).
% 1.42/0.58  fof(f442,plain,(
% 1.42/0.58    ~r2_hidden(sK5,k2_tarski(sK5,sK5)) | ~spl10_1),
% 1.42/0.58    inference(superposition,[],[f221,f441])).
% 1.42/0.58  fof(f441,plain,(
% 1.42/0.58    sK5 = k4_tarski(k4_tarski(sK5,k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) | ~spl10_1),
% 1.42/0.58    inference(forward_demodulation,[],[f396,f88])).
% 1.42/0.58  fof(f88,plain,(
% 1.42/0.58    sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) | ~spl10_1),
% 1.42/0.58    inference(avatar_component_clause,[],[f86])).
% 1.42/0.58  fof(f86,plain,(
% 1.42/0.58    spl10_1 <=> sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.42/0.58  fof(f396,plain,(
% 1.42/0.58    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))),
% 1.42/0.58    inference(subsumption_resolution,[],[f395,f42])).
% 1.42/0.58  fof(f42,plain,(
% 1.42/0.58    k1_xboole_0 != sK2),
% 1.42/0.58    inference(cnf_transformation,[],[f22])).
% 1.42/0.58  fof(f22,plain,(
% 1.42/0.58    ((sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2),
% 1.42/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f21,f20])).
% 1.42/0.58  fof(f20,plain,(
% 1.42/0.58    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2)),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f21,plain,(
% 1.42/0.58    ? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) => ((sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)))),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f12,plain,(
% 1.42/0.58    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.42/0.58    inference(ennf_transformation,[],[f11])).
% 1.42/0.58  fof(f11,negated_conjecture,(
% 1.42/0.58    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.42/0.58    inference(negated_conjecture,[],[f10])).
% 1.42/0.58  fof(f10,conjecture,(
% 1.42/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.42/0.58  fof(f395,plain,(
% 1.42/0.58    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) | k1_xboole_0 = sK2),
% 1.42/0.58    inference(subsumption_resolution,[],[f394,f43])).
% 1.42/0.58  fof(f43,plain,(
% 1.42/0.58    k1_xboole_0 != sK3),
% 1.42/0.58    inference(cnf_transformation,[],[f22])).
% 1.42/0.58  fof(f394,plain,(
% 1.42/0.58    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.42/0.58    inference(subsumption_resolution,[],[f393,f44])).
% 1.42/0.58  fof(f44,plain,(
% 1.42/0.58    k1_xboole_0 != sK4),
% 1.42/0.58    inference(cnf_transformation,[],[f22])).
% 1.42/0.58  fof(f393,plain,(
% 1.42/0.58    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.42/0.58    inference(resolution,[],[f80,f77])).
% 1.42/0.58  fof(f77,plain,(
% 1.42/0.58    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.42/0.58    inference(definition_unfolding,[],[f45,f55])).
% 1.42/0.58  fof(f55,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f6])).
% 1.42/0.58  fof(f6,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.42/0.58  fof(f45,plain,(
% 1.42/0.58    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))),
% 1.42/0.58    inference(cnf_transformation,[],[f22])).
% 1.42/0.58  fof(f80,plain,(
% 1.42/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(definition_unfolding,[],[f76,f56,f55])).
% 1.42/0.58  fof(f56,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f5])).
% 1.42/0.58  fof(f5,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.42/0.58  fof(f76,plain,(
% 1.42/0.58    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f15])).
% 1.42/0.58  fof(f15,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.42/0.58    inference(ennf_transformation,[],[f8])).
% 1.42/0.58  fof(f8,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.42/0.58  fof(f221,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_tarski(k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2)))) )),
% 1.42/0.58    inference(equality_resolution,[],[f218])).
% 1.42/0.58  fof(f218,plain,(
% 1.42/0.58    ( ! [X12,X10,X13,X11] : (k4_tarski(k4_tarski(X11,X12),X13) != X10 | ~r2_hidden(X11,k2_tarski(X10,X10))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f215,f137])).
% 1.42/0.58  fof(f137,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) != k1_xboole_0) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f136,f101])).
% 1.42/0.58  fof(f101,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.42/0.58    inference(resolution,[],[f83,f84])).
% 1.42/0.58  fof(f83,plain,(
% 1.42/0.58    ( ! [X4,X2,X0] : (~sP1(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.42/0.58    inference(equality_resolution,[],[f66])).
% 1.42/0.58  fof(f66,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP1(X0,X1,X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f38])).
% 1.42/0.58  fof(f136,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) != k1_xboole_0 | ~r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.42/0.58    inference(superposition,[],[f73,f118])).
% 1.42/0.58  fof(f118,plain,(
% 1.42/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.42/0.58    inference(duplicate_literal_removal,[],[f116])).
% 1.42/0.58  fof(f116,plain,(
% 1.42/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.42/0.58    inference(resolution,[],[f109,f105])).
% 1.42/0.58  fof(f105,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r2_hidden(sK6(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.42/0.58    inference(resolution,[],[f104,f47])).
% 1.42/0.58  fof(f47,plain,(
% 1.42/0.58    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f24])).
% 1.42/0.58  fof(f24,plain,(
% 1.42/0.58    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 1.42/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f23])).
% 1.42/0.58  fof(f23,plain,(
% 1.42/0.58    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f13,plain,(
% 1.42/0.58    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.42/0.58    inference(ennf_transformation,[],[f9])).
% 1.42/0.58  fof(f9,axiom,(
% 1.42/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.42/0.58  fof(f104,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 1.42/0.58    inference(resolution,[],[f57,f81])).
% 1.42/0.58  fof(f81,plain,(
% 1.42/0.58    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.42/0.58    inference(equality_resolution,[],[f63])).
% 1.42/0.58  fof(f63,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.42/0.58    inference(cnf_transformation,[],[f33])).
% 1.42/0.58  fof(f33,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.58    inference(nnf_transformation,[],[f17])).
% 1.42/0.58  fof(f17,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.42/0.58    inference(definition_folding,[],[f1,f16])).
% 1.42/0.58  fof(f16,plain,(
% 1.42/0.58    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.42/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/0.58  fof(f1,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.42/0.58  fof(f57,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f32])).
% 1.42/0.58  fof(f32,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X0) & r2_hidden(sK8(X0,X1,X2),X1)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.42/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f31])).
% 1.42/0.58  fof(f31,plain,(
% 1.42/0.58    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X0) & r2_hidden(sK8(X0,X1,X2),X1)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f30,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.42/0.58    inference(rectify,[],[f29])).
% 1.42/0.58  fof(f29,plain,(
% 1.42/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.42/0.58    inference(flattening,[],[f28])).
% 1.42/0.58  fof(f28,plain,(
% 1.42/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.42/0.58    inference(nnf_transformation,[],[f16])).
% 1.42/0.58  fof(f109,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r2_hidden(sK6(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.42/0.58    inference(resolution,[],[f108,f47])).
% 1.42/0.58  fof(f108,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 1.42/0.58    inference(resolution,[],[f58,f81])).
% 1.42/0.58  fof(f58,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f32])).
% 1.42/0.58  fof(f73,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f41])).
% 1.42/0.58  fof(f41,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.42/0.58    inference(flattening,[],[f40])).
% 1.42/0.58  fof(f40,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.42/0.58    inference(nnf_transformation,[],[f4])).
% 1.42/0.58  fof(f4,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.42/0.58  fof(f215,plain,(
% 1.42/0.58    ( ! [X12,X10,X13,X11] : (k4_tarski(k4_tarski(X11,X12),X13) != X10 | ~r2_hidden(X11,k2_tarski(X10,X10)) | k1_xboole_0 = k2_tarski(X10,X10)) )),
% 1.42/0.58    inference(superposition,[],[f79,f209])).
% 1.42/0.58  fof(f209,plain,(
% 1.42/0.58    ( ! [X0] : (sK7(k2_tarski(X0,X0)) = X0) )),
% 1.42/0.58    inference(equality_resolution,[],[f205])).
% 1.42/0.58  fof(f205,plain,(
% 1.42/0.58    ( ! [X0,X1] : (X0 != X1 | sK7(k2_tarski(X0,X1)) = X1) )),
% 1.42/0.58    inference(equality_factoring,[],[f173])).
% 1.42/0.58  fof(f173,plain,(
% 1.42/0.58    ( ! [X10,X9] : (sK7(k2_tarski(X9,X10)) = X9 | sK7(k2_tarski(X9,X10)) = X10) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f169,f137])).
% 1.42/0.58  fof(f169,plain,(
% 1.42/0.58    ( ! [X10,X9] : (sK7(k2_tarski(X9,X10)) = X9 | sK7(k2_tarski(X9,X10)) = X10 | k1_xboole_0 = k2_tarski(X9,X10)) )),
% 1.42/0.58    inference(resolution,[],[f164,f50])).
% 1.42/0.58  fof(f50,plain,(
% 1.42/0.58    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f26])).
% 1.42/0.58  fof(f26,plain,(
% 1.42/0.58    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 1.42/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f14,f25])).
% 1.42/0.58  fof(f25,plain,(
% 1.42/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)))),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f14,plain,(
% 1.42/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.42/0.58    inference(ennf_transformation,[],[f7])).
% 1.42/0.58  fof(f7,axiom,(
% 1.42/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.42/0.58  fof(f164,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.42/0.58    inference(resolution,[],[f65,f84])).
% 1.42/0.58  fof(f65,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.42/0.58    inference(cnf_transformation,[],[f38])).
% 1.42/0.58  fof(f79,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X3] : (sK7(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(definition_unfolding,[],[f51,f56])).
% 1.42/0.58  fof(f51,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK7(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f26])).
% 1.42/0.58  fof(f440,plain,(
% 1.42/0.58    ~spl10_3),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f439])).
% 1.42/0.58  fof(f439,plain,(
% 1.42/0.58    $false | ~spl10_3),
% 1.42/0.58    inference(subsumption_resolution,[],[f432,f100])).
% 1.42/0.58  fof(f432,plain,(
% 1.42/0.58    ~r2_hidden(sK5,k2_tarski(sK5,sK5)) | ~spl10_3),
% 1.42/0.58    inference(superposition,[],[f195,f419])).
% 1.42/0.58  fof(f419,plain,(
% 1.42/0.58    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),sK5) | ~spl10_3),
% 1.42/0.58    inference(forward_demodulation,[],[f396,f96])).
% 1.42/0.58  fof(f96,plain,(
% 1.42/0.58    sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | ~spl10_3),
% 1.42/0.58    inference(avatar_component_clause,[],[f94])).
% 1.42/0.58  fof(f94,plain,(
% 1.42/0.58    spl10_3 <=> sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.42/0.58  fof(f195,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_tarski(k4_tarski(X1,X0),k4_tarski(X1,X0)))) )),
% 1.42/0.58    inference(equality_resolution,[],[f192])).
% 1.42/0.58  fof(f192,plain,(
% 1.42/0.58    ( ! [X4,X2,X3] : (k4_tarski(X3,X4) != X2 | ~r2_hidden(X4,k2_tarski(X2,X2))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f189,f137])).
% 1.42/0.58  fof(f189,plain,(
% 1.42/0.58    ( ! [X4,X2,X3] : (k4_tarski(X3,X4) != X2 | ~r2_hidden(X4,k2_tarski(X2,X2)) | k1_xboole_0 = k2_tarski(X2,X2)) )),
% 1.42/0.58    inference(superposition,[],[f49,f188])).
% 1.42/0.58  fof(f188,plain,(
% 1.42/0.58    ( ! [X0] : (sK6(k2_tarski(X0,X0)) = X0) )),
% 1.42/0.58    inference(equality_resolution,[],[f182])).
% 1.42/0.58  fof(f182,plain,(
% 1.42/0.58    ( ! [X0,X1] : (X0 != X1 | sK6(k2_tarski(X0,X1)) = X1) )),
% 1.42/0.58    inference(equality_factoring,[],[f172])).
% 1.42/0.58  fof(f172,plain,(
% 1.42/0.58    ( ! [X4,X5] : (sK6(k2_tarski(X4,X5)) = X4 | sK6(k2_tarski(X4,X5)) = X5) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f167,f137])).
% 1.42/0.58  fof(f167,plain,(
% 1.42/0.58    ( ! [X4,X5] : (sK6(k2_tarski(X4,X5)) = X4 | sK6(k2_tarski(X4,X5)) = X5 | k1_xboole_0 = k2_tarski(X4,X5)) )),
% 1.42/0.58    inference(resolution,[],[f164,f47])).
% 1.42/0.58  fof(f49,plain,(
% 1.42/0.58    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK6(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f24])).
% 1.42/0.58  fof(f417,plain,(
% 1.42/0.58    ~spl10_2),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f416])).
% 1.42/0.58  fof(f416,plain,(
% 1.42/0.58    $false | ~spl10_2),
% 1.42/0.58    inference(subsumption_resolution,[],[f399,f100])).
% 1.42/0.58  fof(f399,plain,(
% 1.42/0.58    ~r2_hidden(sK5,k2_tarski(sK5,sK5)) | ~spl10_2),
% 1.42/0.58    inference(superposition,[],[f220,f397])).
% 1.42/0.58  fof(f397,plain,(
% 1.42/0.58    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),sK5),k7_mcart_1(sK2,sK3,sK4,sK5)) | ~spl10_2),
% 1.42/0.58    inference(forward_demodulation,[],[f396,f92])).
% 1.42/0.58  fof(f92,plain,(
% 1.42/0.58    sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | ~spl10_2),
% 1.42/0.58    inference(avatar_component_clause,[],[f90])).
% 1.42/0.58  fof(f90,plain,(
% 1.42/0.58    spl10_2 <=> sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.42/0.58  fof(f220,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_tarski(k4_tarski(k4_tarski(X1,X0),X2),k4_tarski(k4_tarski(X1,X0),X2)))) )),
% 1.42/0.58    inference(equality_resolution,[],[f212])).
% 1.42/0.58  fof(f212,plain,(
% 1.42/0.58    ( ! [X4,X2,X5,X3] : (k4_tarski(k4_tarski(X3,X4),X5) != X2 | ~r2_hidden(X4,k2_tarski(X2,X2))) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f210,f137])).
% 1.42/0.58  fof(f210,plain,(
% 1.42/0.58    ( ! [X4,X2,X5,X3] : (k4_tarski(k4_tarski(X3,X4),X5) != X2 | ~r2_hidden(X4,k2_tarski(X2,X2)) | k1_xboole_0 = k2_tarski(X2,X2)) )),
% 1.42/0.58    inference(superposition,[],[f78,f209])).
% 1.42/0.58  fof(f78,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X3] : (sK7(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(definition_unfolding,[],[f52,f56])).
% 1.42/0.58  fof(f52,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK7(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.42/0.58    inference(cnf_transformation,[],[f26])).
% 1.42/0.58  fof(f97,plain,(
% 1.42/0.58    spl10_1 | spl10_2 | spl10_3),
% 1.42/0.58    inference(avatar_split_clause,[],[f46,f94,f90,f86])).
% 1.42/0.58  fof(f46,plain,(
% 1.42/0.58    sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)),
% 1.42/0.58    inference(cnf_transformation,[],[f22])).
% 1.42/0.58  % SZS output end Proof for theBenchmark
% 1.42/0.58  % (4972)------------------------------
% 1.42/0.58  % (4972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (4972)Termination reason: Refutation
% 1.42/0.58  
% 1.42/0.58  % (4972)Memory used [KB]: 11001
% 1.42/0.58  % (4972)Time elapsed: 0.138 s
% 1.42/0.58  % (4972)------------------------------
% 1.42/0.58  % (4972)------------------------------
% 1.42/0.60  % (4965)Success in time 0.228 s
%------------------------------------------------------------------------------
