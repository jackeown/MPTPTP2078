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
% DateTime   : Thu Dec  3 12:41:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 403 expanded)
%              Number of leaves         :   20 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  381 (1846 expanded)
%              Number of equality atoms :  101 ( 297 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f87,f273,f277,f296,f329,f358])).

fof(f358,plain,
    ( spl14_2
    | ~ spl14_4 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl14_2
    | ~ spl14_4 ),
    inference(trivial_inequality_removal,[],[f356])).

fof(f356,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl14_2
    | ~ spl14_4 ),
    inference(superposition,[],[f80,f335])).

fof(f335,plain,
    ( k1_xboole_0 = sK3
    | ~ spl14_4 ),
    inference(resolution,[],[f292,f176])).

fof(f176,plain,(
    ! [X5] :
      ( r2_hidden(sK6(k1_xboole_0,X5),X5)
      | k1_xboole_0 = X5 ) ),
    inference(backward_demodulation,[],[f138,f158])).

fof(f158,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f138,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f48,f45])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f138,plain,(
    ! [X5] :
      ( r2_hidden(sK6(k1_xboole_0,X5),X5)
      | k3_tarski(k1_xboole_0) = X5 ) ),
    inference(resolution,[],[f133,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f6,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f133,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,X0)
      | r2_hidden(sK6(k1_xboole_0,X0),X0) ) ),
    inference(resolution,[],[f56,f91])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | sP0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK6(X0,X1),X3) )
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( ( r2_hidden(sK7(X0,X1),X0)
              & r2_hidden(sK6(X0,X1),sK7(X0,X1)) )
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK8(X0,X5),X0)
                & r2_hidden(X5,sK8(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK6(X0,X1),X3) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK6(X0,X1),X4) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK6(X0,X1),X4) )
     => ( r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK8(X0,X5),X0)
        & r2_hidden(X5,sK8(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f292,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK3)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl14_4
  <=> ! [X4] : ~ r2_hidden(X4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f80,plain,
    ( k1_xboole_0 != sK3
    | spl14_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl14_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f329,plain,
    ( spl14_3
    | ~ spl14_5 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl14_3
    | ~ spl14_5 ),
    inference(trivial_inequality_removal,[],[f327])).

fof(f327,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl14_3
    | ~ spl14_5 ),
    inference(superposition,[],[f85,f306])).

fof(f306,plain,
    ( k1_xboole_0 = sK2
    | ~ spl14_5 ),
    inference(resolution,[],[f295,f176])).

fof(f295,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK2)
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl14_5
  <=> ! [X3] : ~ r2_hidden(X3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f85,plain,
    ( k1_xboole_0 != sK2
    | spl14_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl14_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f296,plain,
    ( spl14_4
    | spl14_5
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f286,f74,f294,f291])).

fof(f74,plain,
    ( spl14_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f286,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,sK2)
        | ~ r2_hidden(X4,sK3) )
    | ~ spl14_1 ),
    inference(resolution,[],[f284,f278])).

fof(f278,plain,
    ( sP1(sK3,sK2,k1_xboole_0)
    | ~ spl14_1 ),
    inference(superposition,[],[f72,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f72,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

% (8175)Termination reason: Refutation not found, incomplete strategy
fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

% (8175)Memory used [KB]: 6140
% (8175)Time elapsed: 0.136 s
% (8175)------------------------------
% (8175)------------------------------
fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f5,f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f284,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X1,X3,k1_xboole_0)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f71,f91])).

fof(f71,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK9(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2))
              & r2_hidden(sK11(X0,X1,X2),X0)
              & r2_hidden(sK10(X0,X1,X2),X1) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8
                & r2_hidden(sK13(X0,X1,X8),X0)
                & r2_hidden(sK12(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f35,f38,f37,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK9(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK9(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK9(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2))
        & r2_hidden(sK11(X0,X1,X2),X0)
        & r2_hidden(sK10(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8
        & r2_hidden(sK13(X0,X1,X8),X0)
        & r2_hidden(sK12(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f277,plain,
    ( spl14_1
    | ~ spl14_3 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl14_1
    | ~ spl14_3 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl14_1
    | ~ spl14_3 ),
    inference(superposition,[],[f274,f225])).

fof(f225,plain,(
    ! [X9] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X9) ),
    inference(resolution,[],[f220,f176])).

fof(f220,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f157,f91])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X2,X1,X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f60,f72])).

fof(f60,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X8,X2)
      | r2_hidden(sK12(X0,X1,X8),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f274,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl14_1
    | ~ spl14_3 ),
    inference(backward_demodulation,[],[f76,f84])).

fof(f84,plain,
    ( k1_xboole_0 = sK2
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f76,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f273,plain,
    ( spl14_1
    | ~ spl14_2 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl14_1
    | ~ spl14_2 ),
    inference(trivial_inequality_removal,[],[f270])).

fof(f270,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl14_1
    | ~ spl14_2 ),
    inference(superposition,[],[f88,f251])).

fof(f251,plain,(
    ! [X9] : k1_xboole_0 = k2_zfmisc_1(X9,k1_xboole_0) ),
    inference(resolution,[],[f245,f176])).

fof(f245,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f241,f72])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(k1_xboole_0,X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f61,f91])).

fof(f61,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK13(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0)
    | spl14_1
    | ~ spl14_2 ),
    inference(forward_demodulation,[],[f76,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK3
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f78])).

% (8198)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f87,plain,
    ( spl14_1
    | spl14_3
    | spl14_2 ),
    inference(avatar_split_clause,[],[f41,f78,f83,f74])).

fof(f41,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2 )
      | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2 )
        | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ) ),
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f86,plain,
    ( ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f42,f83,f74])).

fof(f42,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f43,f78,f74])).

fof(f43,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:30:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (8173)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (8173)Refutation not found, incomplete strategy% (8173)------------------------------
% 0.22/0.53  % (8173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8173)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8173)Memory used [KB]: 10618
% 0.22/0.53  % (8173)Time elapsed: 0.110 s
% 0.22/0.53  % (8173)------------------------------
% 0.22/0.53  % (8173)------------------------------
% 0.22/0.54  % (8183)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (8189)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (8194)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (8184)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (8181)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (8177)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (8183)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (8181)Refutation not found, incomplete strategy% (8181)------------------------------
% 0.22/0.55  % (8181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8171)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (8181)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8181)Memory used [KB]: 10618
% 0.22/0.55  % (8181)Time elapsed: 0.125 s
% 0.22/0.55  % (8181)------------------------------
% 0.22/0.55  % (8181)------------------------------
% 0.22/0.55  % (8171)Refutation not found, incomplete strategy% (8171)------------------------------
% 0.22/0.55  % (8171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8171)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8171)Memory used [KB]: 1663
% 0.22/0.55  % (8171)Time elapsed: 0.126 s
% 0.22/0.55  % (8171)------------------------------
% 0.22/0.55  % (8171)------------------------------
% 0.22/0.56  % (8186)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (8175)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (8175)Refutation not found, incomplete strategy% (8175)------------------------------
% 0.22/0.56  % (8175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f359,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f81,f86,f87,f273,f277,f296,f329,f358])).
% 0.22/0.56  fof(f358,plain,(
% 0.22/0.56    spl14_2 | ~spl14_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f357])).
% 0.22/0.56  fof(f357,plain,(
% 0.22/0.56    $false | (spl14_2 | ~spl14_4)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f356])).
% 0.22/0.56  fof(f356,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | (spl14_2 | ~spl14_4)),
% 0.22/0.56    inference(superposition,[],[f80,f335])).
% 0.22/0.56  fof(f335,plain,(
% 0.22/0.56    k1_xboole_0 = sK3 | ~spl14_4),
% 0.22/0.56    inference(resolution,[],[f292,f176])).
% 0.22/0.56  fof(f176,plain,(
% 0.22/0.56    ( ! [X5] : (r2_hidden(sK6(k1_xboole_0,X5),X5) | k1_xboole_0 = X5) )),
% 0.22/0.56    inference(backward_demodulation,[],[f138,f158])).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.56    inference(resolution,[],[f138,f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(condensation,[],[f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f48,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    ( ! [X5] : (r2_hidden(sK6(k1_xboole_0,X5),X5) | k3_tarski(k1_xboole_0) = X5) )),
% 0.22/0.56    inference(resolution,[],[f133,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~sP0(X0,X1) | k3_tarski(X0) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k3_tarski(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP0(X0,X1))),
% 0.22/0.56    inference(definition_folding,[],[f6,f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    ( ! [X0] : (sP0(k1_xboole_0,X0) | r2_hidden(sK6(k1_xboole_0,X0),X0)) )),
% 0.22/0.56    inference(resolution,[],[f56,f91])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | sP0(X0,X1) | r2_hidden(sK6(X0,X1),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK6(X0,X1),X3)) | ~r2_hidden(sK6(X0,X1),X1)) & ((r2_hidden(sK7(X0,X1),X0) & r2_hidden(sK6(X0,X1),sK7(X0,X1))) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK8(X0,X5),X0) & r2_hidden(X5,sK8(X0,X5))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f28,f31,f30,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK6(X0,X1),X3)) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK6(X0,X1),X4)) | r2_hidden(sK6(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK6(X0,X1),X4)) => (r2_hidden(sK7(X0,X1),X0) & r2_hidden(sK6(X0,X1),sK7(X0,X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK8(X0,X5),X0) & r2_hidden(X5,sK8(X0,X5))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f13])).
% 0.22/0.56  fof(f292,plain,(
% 0.22/0.56    ( ! [X4] : (~r2_hidden(X4,sK3)) ) | ~spl14_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f291])).
% 0.22/0.56  fof(f291,plain,(
% 0.22/0.56    spl14_4 <=> ! [X4] : ~r2_hidden(X4,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    k1_xboole_0 != sK3 | spl14_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    spl14_2 <=> k1_xboole_0 = sK3),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.22/0.56  fof(f329,plain,(
% 0.22/0.56    spl14_3 | ~spl14_5),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f328])).
% 0.22/0.56  fof(f328,plain,(
% 0.22/0.56    $false | (spl14_3 | ~spl14_5)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f327])).
% 0.22/0.56  fof(f327,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | (spl14_3 | ~spl14_5)),
% 0.22/0.56    inference(superposition,[],[f85,f306])).
% 0.22/0.56  fof(f306,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | ~spl14_5),
% 0.22/0.56    inference(resolution,[],[f295,f176])).
% 0.22/0.56  fof(f295,plain,(
% 0.22/0.56    ( ! [X3] : (~r2_hidden(X3,sK2)) ) | ~spl14_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f294])).
% 0.22/0.56  fof(f294,plain,(
% 0.22/0.56    spl14_5 <=> ! [X3] : ~r2_hidden(X3,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    k1_xboole_0 != sK2 | spl14_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f83])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    spl14_3 <=> k1_xboole_0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 0.22/0.56  fof(f296,plain,(
% 0.22/0.56    spl14_4 | spl14_5 | ~spl14_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f286,f74,f294,f291])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    spl14_1 <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.22/0.56  fof(f286,plain,(
% 0.22/0.56    ( ! [X4,X3] : (~r2_hidden(X3,sK2) | ~r2_hidden(X4,sK3)) ) | ~spl14_1),
% 0.22/0.56    inference(resolution,[],[f284,f278])).
% 0.22/0.56  fof(f278,plain,(
% 0.22/0.56    sP1(sK3,sK2,k1_xboole_0) | ~spl14_1),
% 0.22/0.56    inference(superposition,[],[f72,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | ~spl14_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f74])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sP1(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(equality_resolution,[],[f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  % (8175)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f16])).
% 0.22/0.56  
% 0.22/0.56  % (8175)Memory used [KB]: 6140
% 0.22/0.56  % (8175)Time elapsed: 0.136 s
% 0.22/0.56  % (8175)------------------------------
% 0.22/0.56  % (8175)------------------------------
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 0.22/0.56    inference(definition_folding,[],[f5,f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.56  fof(f284,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~sP1(X1,X3,k1_xboole_0) | ~r2_hidden(X2,X3) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f71,f91])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP1(X0,X1,X2)) )),
% 0.22/0.56    inference(equality_resolution,[],[f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) & r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK10(X0,X1,X2),X1)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 & r2_hidden(sK13(X0,X1,X8),X0) & r2_hidden(sK12(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f35,f38,f37,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK9(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK9(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) & r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK10(X0,X1,X2),X1)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 & r2_hidden(sK13(X0,X1,X8),X0) & r2_hidden(sK12(X0,X1,X8),X1)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.56    inference(rectify,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.22/0.56    inference(nnf_transformation,[],[f15])).
% 0.22/0.56  fof(f277,plain,(
% 0.22/0.56    spl14_1 | ~spl14_3),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f276])).
% 0.22/0.56  fof(f276,plain,(
% 0.22/0.56    $false | (spl14_1 | ~spl14_3)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f275])).
% 0.22/0.56  fof(f275,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | (spl14_1 | ~spl14_3)),
% 0.22/0.56    inference(superposition,[],[f274,f225])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X9)) )),
% 0.22/0.56    inference(resolution,[],[f220,f176])).
% 0.22/0.56  fof(f220,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.22/0.56    inference(resolution,[],[f157,f91])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK12(X2,X1,X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.56    inference(resolution,[],[f60,f72])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X2,X0,X8,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X8,X2) | r2_hidden(sK12(X0,X1,X8),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f274,plain,(
% 0.22/0.56    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl14_1 | ~spl14_3)),
% 0.22/0.56    inference(backward_demodulation,[],[f76,f84])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | ~spl14_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f83])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) | spl14_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f74])).
% 0.22/0.56  fof(f273,plain,(
% 0.22/0.56    spl14_1 | ~spl14_2),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f272])).
% 0.22/0.56  fof(f272,plain,(
% 0.22/0.56    $false | (spl14_1 | ~spl14_2)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f270])).
% 0.22/0.56  fof(f270,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | (spl14_1 | ~spl14_2)),
% 0.22/0.56    inference(superposition,[],[f88,f251])).
% 0.22/0.56  fof(f251,plain,(
% 0.22/0.56    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(X9,k1_xboole_0)) )),
% 0.22/0.56    inference(resolution,[],[f245,f176])).
% 0.22/0.56  fof(f245,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 0.22/0.56    inference(resolution,[],[f241,f72])).
% 0.22/0.56  fof(f241,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~sP1(k1_xboole_0,X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f61,f91])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X2,X0,X8,X1] : (r2_hidden(sK13(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | ~sP1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0) | (spl14_1 | ~spl14_2)),
% 0.22/0.56    inference(forward_demodulation,[],[f76,f79])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    k1_xboole_0 = sK3 | ~spl14_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f78])).
% 0.22/0.56  % (8198)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    spl14_1 | spl14_3 | spl14_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f41,f78,f83,f74])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ((k1_xboole_0 != sK3 & k1_xboole_0 != sK2) | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)) & (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK3 & k1_xboole_0 != sK2) | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)) & (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    inference(negated_conjecture,[],[f7])).
% 0.22/0.56  fof(f7,conjecture,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ~spl14_1 | ~spl14_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f42,f83,f74])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ~spl14_1 | ~spl14_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f43,f78,f74])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    k1_xboole_0 != sK3 | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (8183)------------------------------
% 0.22/0.56  % (8183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8183)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (8183)Memory used [KB]: 6268
% 0.22/0.56  % (8183)Time elapsed: 0.125 s
% 0.22/0.56  % (8183)------------------------------
% 0.22/0.56  % (8183)------------------------------
% 0.22/0.57  % (8170)Success in time 0.2 s
%------------------------------------------------------------------------------
