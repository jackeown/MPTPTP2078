%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 305 expanded)
%              Number of leaves         :   25 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  377 ( 992 expanded)
%              Number of equality atoms :  175 ( 578 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f200,f229,f232,f240,f297,f305])).

fof(f305,plain,
    ( spl10_8
    | ~ spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f149,f109,f136,f218])).

fof(f218,plain,
    ( spl10_8
  <=> ! [X6] : r2_hidden(sK1,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f136,plain,
    ( spl10_4
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f109,plain,
    ( spl10_2
  <=> sK1 = k2_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f149,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,k1_xboole_0)
        | r2_hidden(sK1,X1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f145,f100])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,k2_zfmisc_1(X0,X1))
        | r2_hidden(sK1,X1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f82,f119])).

fof(f119,plain,
    ( sK1 = k4_tarski(sK2,sK1)
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f49,f118])).

fof(f118,plain,
    ( sK1 = sK3
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f117,f111])).

% (27703)Termination reason: Refutation not found, incomplete strategy
fof(f111,plain,
    ( sK1 = k2_mcart_1(sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f109])).

% (27703)Memory used [KB]: 6268
fof(f117,plain,(
    k2_mcart_1(sK1) = sK3 ),
    inference(superposition,[],[f61,f49])).

% (27703)Time elapsed: 0.118 s
fof(f61,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f12])).

% (27703)------------------------------
% (27703)------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f49,plain,(
    sK1 = k4_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK1 = k2_mcart_1(sK1)
      | sK1 = k1_mcart_1(sK1) )
    & sK1 = k4_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK1 = k2_mcart_1(sK1)
        | sK1 = k1_mcart_1(sK1) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK1 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK1
   => sK1 = k4_tarski(sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f297,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl10_1
    | spl10_4 ),
    inference(subsumption_resolution,[],[f290,f138])).

fof(f138,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f290,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl10_1 ),
    inference(superposition,[],[f125,f283])).

fof(f283,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f282,f97])).

fof(f97,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f63,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK8(X0,X1) != X0
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sK8(X0,X1) = X0
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK8(X0,X1) != X0
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sK8(X0,X1) = X0
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f282,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl10_1 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl10_1 ),
    inference(resolution,[],[f255,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f30])).

fof(f30,plain,(
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

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl10_1 ),
    inference(extensionality_resolution,[],[f98,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( sK1 != sK6(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl10_1 ),
    inference(superposition,[],[f56,f207])).

fof(f207,plain,
    ( sK1 = k4_tarski(sK1,sK3)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f49,f201])).

fof(f201,plain,
    ( sK1 = sK2
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f116,f107])).

fof(f107,plain,
    ( sK1 = k1_mcart_1(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl10_1
  <=> sK1 = k1_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f116,plain,(
    k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[],[f60,f49])).

fof(f60,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK6(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f85])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f125,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f103,f102])).

fof(f102,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f103,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f79,f84])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f240,plain,(
    ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl10_10 ),
    inference(resolution,[],[f228,f124])).

fof(f124,plain,(
    ! [X0] : ~ r2_hidden(X0,sK7(k1_zfmisc_1(X0))) ),
    inference(resolution,[],[f122,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f122,plain,(
    ! [X0] : r1_tarski(sK7(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f8,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f228,plain,
    ( ! [X7] : r2_hidden(sK3,X7)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl10_10
  <=> ! [X7] : r2_hidden(sK3,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f232,plain,(
    ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl10_8 ),
    inference(resolution,[],[f219,f124])).

fof(f219,plain,
    ( ! [X6] : r2_hidden(sK1,X6)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f218])).

fof(f229,plain,
    ( spl10_10
    | ~ spl10_4
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f216,f105,f136,f227])).

fof(f216,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK1,k1_xboole_0)
        | r2_hidden(sK3,X7) )
    | ~ spl10_1 ),
    inference(superposition,[],[f147,f207])).

fof(f147,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_xboole_0)
      | r2_hidden(X5,X3) ) ),
    inference(superposition,[],[f82,f100])).

fof(f200,plain,
    ( ~ spl10_2
    | spl10_4 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl10_2
    | spl10_4 ),
    inference(subsumption_resolution,[],[f193,f138])).

fof(f193,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl10_2 ),
    inference(superposition,[],[f125,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f184,f97])).

fof(f184,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl10_2 ),
    inference(resolution,[],[f181,f55])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl10_2 ),
    inference(extensionality_resolution,[],[f98,f180])).

fof(f180,plain,
    ( ! [X0] :
        ( sK1 != sK6(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl10_2 ),
    inference(superposition,[],[f57,f119])).

fof(f57,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK6(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f112,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f50,f109,f105])).

fof(f50,plain,
    ( sK1 = k2_mcart_1(sK1)
    | sK1 = k1_mcart_1(sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:28:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (27684)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (27703)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (27681)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (27702)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (27680)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (27695)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (27703)Refutation not found, incomplete strategy% (27703)------------------------------
% 0.21/0.53  % (27703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27684)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f308,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f112,f200,f229,f232,f240,f297,f305])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    spl10_8 | ~spl10_4 | ~spl10_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f149,f109,f136,f218])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    spl10_8 <=> ! [X6] : r2_hidden(sK1,X6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl10_4 <=> r2_hidden(sK1,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl10_2 <=> sK1 = k2_mcart_1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK1,k1_xboole_0) | r2_hidden(sK1,X1)) ) | ~spl10_2),
% 0.21/0.53    inference(superposition,[],[f145,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.53    inference(flattening,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.53    inference(nnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK1,k2_zfmisc_1(X0,X1)) | r2_hidden(sK1,X1)) ) | ~spl10_2),
% 0.21/0.53    inference(superposition,[],[f82,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    sK1 = k4_tarski(sK2,sK1) | ~spl10_2),
% 0.21/0.53    inference(backward_demodulation,[],[f49,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    sK1 = sK3 | ~spl10_2),
% 0.21/0.53    inference(forward_demodulation,[],[f117,f111])).
% 0.21/0.53  % (27703)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    sK1 = k2_mcart_1(sK1) | ~spl10_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  
% 0.21/0.53  % (27703)Memory used [KB]: 6268
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    k2_mcart_1(sK1) = sK3),
% 0.21/0.53    inference(superposition,[],[f61,f49])).
% 0.21/0.53  % (27703)Time elapsed: 0.118 s
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  % (27703)------------------------------
% 0.21/0.53  % (27703)------------------------------
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    (sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f24,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & ? [X2,X1] : k4_tarski(X1,X2) = sK1)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X2,X1] : k4_tarski(X1,X2) = sK1 => sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.53    inference(flattening,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.53    inference(nnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    ~spl10_1 | spl10_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f296])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    $false | (~spl10_1 | spl10_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f290,f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k1_xboole_0) | spl10_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f136])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl10_1),
% 0.21/0.53    inference(superposition,[],[f125,f283])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f282,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 0.21/0.53    inference(equality_resolution,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 0.21/0.53    inference(equality_resolution,[],[f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f63,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f51,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f59,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f35,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl10_1),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f281])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl10_1),
% 0.21/0.53    inference(resolution,[],[f255,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK6(X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl10_1),
% 0.21/0.53    inference(extensionality_resolution,[],[f98,f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 != sK6(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl10_1),
% 0.21/0.53    inference(superposition,[],[f56,f207])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    sK1 = k4_tarski(sK1,sK3) | ~spl10_1),
% 0.21/0.53    inference(forward_demodulation,[],[f49,f201])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    sK1 = sK2 | ~spl10_1),
% 0.21/0.53    inference(backward_demodulation,[],[f116,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    sK1 = k1_mcart_1(sK1) | ~spl10_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl10_1 <=> sK1 = k1_mcart_1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    k1_mcart_1(sK1) = sK2),
% 0.21/0.53    inference(superposition,[],[f60,f49])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK6(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.21/0.53    inference(equality_resolution,[],[f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f62,f85])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.53    inference(resolution,[],[f103,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK9(X0,X1,X2) != X0 & sK9(X0,X1,X2) != X1) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sK9(X0,X1,X2) = X0 | sK9(X0,X1,X2) = X1 | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK9(X0,X1,X2) != X0 & sK9(X0,X1,X2) != X1) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sK9(X0,X1,X2) = X0 | sK9(X0,X1,X2) = X1 | r2_hidden(sK9(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.53    inference(flattening,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP0(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f79,f84])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.53    inference(definition_folding,[],[f2,f21])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    ~spl10_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    $false | ~spl10_10),
% 0.21/0.53    inference(resolution,[],[f228,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK7(k1_zfmisc_1(X0)))) )),
% 0.21/0.53    inference(resolution,[],[f122,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(sK7(k1_zfmisc_1(X0)),X0)) )),
% 0.21/0.53    inference(resolution,[],[f66,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK7(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : m1_subset_1(sK7(X0),X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f8,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK7(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ( ! [X7] : (r2_hidden(sK3,X7)) ) | ~spl10_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f227])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    spl10_10 <=> ! [X7] : r2_hidden(sK3,X7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    ~spl10_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    $false | ~spl10_8),
% 0.21/0.53    inference(resolution,[],[f219,f124])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    ( ! [X6] : (r2_hidden(sK1,X6)) ) | ~spl10_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f218])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    spl10_10 | ~spl10_4 | ~spl10_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f216,f105,f136,f227])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    ( ! [X7] : (~r2_hidden(sK1,k1_xboole_0) | r2_hidden(sK3,X7)) ) | ~spl10_1),
% 0.21/0.53    inference(superposition,[],[f147,f207])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X4,X5),k1_xboole_0) | r2_hidden(X5,X3)) )),
% 0.21/0.53    inference(superposition,[],[f82,f100])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    ~spl10_2 | spl10_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    $false | (~spl10_2 | spl10_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f193,f138])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl10_2),
% 0.21/0.53    inference(superposition,[],[f125,f185])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl10_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f97])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl10_2),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl10_2),
% 0.21/0.53    inference(resolution,[],[f181,f55])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK6(X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl10_2),
% 0.21/0.53    inference(extensionality_resolution,[],[f98,f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 != sK6(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl10_2),
% 0.21/0.53    inference(superposition,[],[f57,f119])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK6(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl10_1 | spl10_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f109,f105])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (27684)------------------------------
% 0.21/0.53  % (27684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27684)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (27684)Memory used [KB]: 10874
% 0.21/0.53  % (27684)Time elapsed: 0.098 s
% 0.21/0.53  % (27684)------------------------------
% 0.21/0.53  % (27684)------------------------------
% 0.21/0.54  % (27687)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (27677)Success in time 0.172 s
%------------------------------------------------------------------------------
