%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:57 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 294 expanded)
%              Number of leaves         :   22 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  299 ( 749 expanded)
%              Number of equality atoms :  115 ( 354 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f81,f151,f156,f167,f173,f179])).

fof(f179,plain,
    ( spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f175,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK0
    | spl8_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f175,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(resolution,[],[f163,f89])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f88,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f88,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f163,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_4
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f173,plain,
    ( spl8_2
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl8_2
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f169,f74])).

fof(f74,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f169,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_5 ),
    inference(resolution,[],[f166,f89])).

fof(f166,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f167,plain,
    ( spl8_4
    | spl8_5
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f160,f68,f165,f162])).

fof(f68,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f157,f88])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f52,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f156,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f154,f124])).

fof(f124,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f89,f90])).

fof(f90,plain,(
    ! [X2,X1] : ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(resolution,[],[f88,f66])).

fof(f66,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f25,f28,f27,f26])).

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
              ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f154,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl8_1
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f70,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f70,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f151,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f82,f125])).

fof(f125,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(X1,k1_xboole_0) ),
    inference(resolution,[],[f89,f91])).

fof(f91,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(X4,k1_xboole_0)) ),
    inference(resolution,[],[f88,f65])).

fof(f65,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f70,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f81,plain,
    ( spl8_1
    | spl8_3
    | spl8_2 ),
    inference(avatar_split_clause,[],[f32,f72,f77,f68])).

fof(f32,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f80,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f33,f77,f68])).

fof(f33,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f34,f72,f68])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n003.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 18:19:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.45  % (6304)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.46  % (6318)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.47  % (6310)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.47  % (6318)Refutation not found, incomplete strategy% (6318)------------------------------
% 0.18/0.47  % (6318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (6318)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.47  
% 0.18/0.47  % (6318)Memory used [KB]: 10618
% 0.18/0.47  % (6318)Time elapsed: 0.074 s
% 0.18/0.47  % (6318)------------------------------
% 0.18/0.47  % (6318)------------------------------
% 0.18/0.47  % (6310)Refutation not found, incomplete strategy% (6310)------------------------------
% 0.18/0.47  % (6310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (6310)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.47  
% 0.18/0.47  % (6310)Memory used [KB]: 10618
% 0.18/0.47  % (6310)Time elapsed: 0.080 s
% 0.18/0.47  % (6310)------------------------------
% 0.18/0.47  % (6310)------------------------------
% 0.18/0.47  % (6304)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f180,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f75,f80,f81,f151,f156,f167,f173,f179])).
% 0.18/0.47  fof(f179,plain,(
% 0.18/0.47    spl8_3 | ~spl8_4),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f178])).
% 0.18/0.47  fof(f178,plain,(
% 0.18/0.47    $false | (spl8_3 | ~spl8_4)),
% 0.18/0.47    inference(subsumption_resolution,[],[f175,f79])).
% 0.18/0.47  fof(f79,plain,(
% 0.18/0.47    k1_xboole_0 != sK0 | spl8_3),
% 0.18/0.47    inference(avatar_component_clause,[],[f77])).
% 0.18/0.47  fof(f77,plain,(
% 0.18/0.47    spl8_3 <=> k1_xboole_0 = sK0),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.18/0.47  fof(f175,plain,(
% 0.18/0.47    k1_xboole_0 = sK0 | ~spl8_4),
% 0.18/0.47    inference(resolution,[],[f163,f89])).
% 0.18/0.47  fof(f89,plain,(
% 0.18/0.47    ( ! [X0] : (r2_hidden(sK2(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.18/0.47    inference(resolution,[],[f88,f37])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | X0 = X1 | r2_hidden(sK2(X0,X1),X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.18/0.47    inference(nnf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.18/0.47    inference(ennf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.18/0.47  fof(f88,plain,(
% 0.18/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.18/0.47    inference(resolution,[],[f61,f35])).
% 0.18/0.47  fof(f35,plain,(
% 0.18/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.18/0.47  fof(f61,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f48,f60])).
% 0.18/0.47  fof(f60,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f36,f59])).
% 0.18/0.47  fof(f59,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f39,f58])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f49,f57])).
% 0.18/0.47  fof(f57,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f53,f56])).
% 0.18/0.47  fof(f56,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f54,f55])).
% 0.18/0.47  fof(f55,plain,(
% 0.18/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.18/0.47  fof(f54,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.18/0.47  fof(f53,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.18/0.47  fof(f39,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f3])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.47  fof(f48,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.18/0.47    inference(ennf_transformation,[],[f11])).
% 0.18/0.47  fof(f11,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.18/0.47  fof(f163,plain,(
% 0.18/0.47    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_4),
% 0.18/0.47    inference(avatar_component_clause,[],[f162])).
% 0.18/0.47  fof(f162,plain,(
% 0.18/0.47    spl8_4 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.18/0.47  fof(f173,plain,(
% 0.18/0.47    spl8_2 | ~spl8_5),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f172])).
% 0.18/0.47  fof(f172,plain,(
% 0.18/0.47    $false | (spl8_2 | ~spl8_5)),
% 0.18/0.47    inference(subsumption_resolution,[],[f169,f74])).
% 0.18/0.47  fof(f74,plain,(
% 0.18/0.47    k1_xboole_0 != sK1 | spl8_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f72])).
% 0.18/0.47  fof(f72,plain,(
% 0.18/0.47    spl8_2 <=> k1_xboole_0 = sK1),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.18/0.47  fof(f169,plain,(
% 0.18/0.47    k1_xboole_0 = sK1 | ~spl8_5),
% 0.18/0.47    inference(resolution,[],[f166,f89])).
% 0.18/0.47  fof(f166,plain,(
% 0.18/0.47    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_5),
% 0.18/0.47    inference(avatar_component_clause,[],[f165])).
% 0.18/0.47  fof(f165,plain,(
% 0.18/0.47    spl8_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.18/0.47  fof(f167,plain,(
% 0.18/0.47    spl8_4 | spl8_5 | ~spl8_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f160,f68,f165,f162])).
% 0.18/0.47  fof(f68,plain,(
% 0.18/0.47    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.18/0.47  fof(f160,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_1),
% 0.18/0.47    inference(subsumption_resolution,[],[f157,f88])).
% 0.18/0.47  fof(f157,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_1),
% 0.18/0.47    inference(superposition,[],[f52,f69])).
% 0.18/0.47  fof(f69,plain,(
% 0.18/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f68])).
% 0.18/0.47  fof(f52,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f31])).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.18/0.47    inference(flattening,[],[f30])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.18/0.47    inference(nnf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.18/0.47  fof(f156,plain,(
% 0.18/0.47    spl8_1 | ~spl8_3),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f155])).
% 0.18/0.47  fof(f155,plain,(
% 0.18/0.47    $false | (spl8_1 | ~spl8_3)),
% 0.18/0.47    inference(subsumption_resolution,[],[f154,f124])).
% 0.18/0.47  fof(f124,plain,(
% 0.18/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.18/0.47    inference(resolution,[],[f89,f90])).
% 0.18/0.47  fof(f90,plain,(
% 0.18/0.47    ( ! [X2,X1] : (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))) )),
% 0.18/0.47    inference(resolution,[],[f88,f66])).
% 0.18/0.47  fof(f66,plain,(
% 0.18/0.47    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.18/0.47    inference(equality_resolution,[],[f40])).
% 0.18/0.47  fof(f40,plain,(
% 0.18/0.47    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.18/0.47    inference(cnf_transformation,[],[f29])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f25,f28,f27,f26])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.47    inference(rectify,[],[f24])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.47    inference(nnf_transformation,[],[f9])).
% 0.18/0.47  fof(f9,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.18/0.47  fof(f154,plain,(
% 0.18/0.47    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl8_1 | ~spl8_3)),
% 0.18/0.47    inference(forward_demodulation,[],[f70,f78])).
% 0.18/0.47  fof(f78,plain,(
% 0.18/0.47    k1_xboole_0 = sK0 | ~spl8_3),
% 0.18/0.47    inference(avatar_component_clause,[],[f77])).
% 0.18/0.47  fof(f70,plain,(
% 0.18/0.47    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl8_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f68])).
% 0.18/0.47  fof(f151,plain,(
% 0.18/0.47    spl8_1 | ~spl8_2),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f150])).
% 0.18/0.47  fof(f150,plain,(
% 0.18/0.47    $false | (spl8_1 | ~spl8_2)),
% 0.18/0.47    inference(trivial_inequality_removal,[],[f149])).
% 0.18/0.47  fof(f149,plain,(
% 0.18/0.47    k1_xboole_0 != k1_xboole_0 | (spl8_1 | ~spl8_2)),
% 0.18/0.47    inference(superposition,[],[f82,f125])).
% 0.18/0.47  fof(f125,plain,(
% 0.18/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(X1,k1_xboole_0)) )),
% 0.18/0.47    inference(resolution,[],[f89,f91])).
% 0.18/0.47  fof(f91,plain,(
% 0.18/0.47    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(X4,k1_xboole_0))) )),
% 0.18/0.47    inference(resolution,[],[f88,f65])).
% 0.18/0.47  fof(f65,plain,(
% 0.18/0.47    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.18/0.47    inference(equality_resolution,[],[f41])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.18/0.47    inference(cnf_transformation,[],[f29])).
% 0.18/0.47  fof(f82,plain,(
% 0.18/0.47    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl8_1 | ~spl8_2)),
% 0.18/0.47    inference(forward_demodulation,[],[f70,f73])).
% 0.18/0.47  fof(f73,plain,(
% 0.18/0.47    k1_xboole_0 = sK1 | ~spl8_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f72])).
% 0.18/0.47  fof(f81,plain,(
% 0.18/0.47    spl8_1 | spl8_3 | spl8_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f32,f72,f77,f68])).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.18/0.47    inference(flattening,[],[f17])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.18/0.47    inference(nnf_transformation,[],[f14])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f13])).
% 0.18/0.47  fof(f13,negated_conjecture,(
% 0.18/0.47    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.47    inference(negated_conjecture,[],[f12])).
% 0.18/0.47  fof(f12,conjecture,(
% 0.18/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.47  fof(f80,plain,(
% 0.18/0.47    ~spl8_1 | ~spl8_3),
% 0.18/0.47    inference(avatar_split_clause,[],[f33,f77,f68])).
% 0.18/0.47  fof(f33,plain,(
% 0.18/0.47    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f20])).
% 0.18/0.47  fof(f75,plain,(
% 0.18/0.47    ~spl8_1 | ~spl8_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f34,f72,f68])).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f20])).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (6304)------------------------------
% 0.18/0.48  % (6304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (6304)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (6304)Memory used [KB]: 10746
% 0.18/0.48  % (6304)Time elapsed: 0.108 s
% 0.18/0.48  % (6304)------------------------------
% 0.18/0.48  % (6304)------------------------------
% 0.18/0.48  % (6300)Success in time 0.145 s
%------------------------------------------------------------------------------
