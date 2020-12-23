%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 490 expanded)
%              Number of leaves         :   15 ( 143 expanded)
%              Depth                    :   14
%              Number of atoms          :  273 (2337 expanded)
%              Number of equality atoms :  105 ( 617 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f923,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f61,f67,f873,f875,f890,f906,f922])).

fof(f922,plain,
    ( spl7_4
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f921])).

fof(f921,plain,
    ( $false
    | spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f908,f60])).

fof(f60,plain,
    ( k1_xboole_0 != sK0
    | spl7_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f908,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6 ),
    inference(resolution,[],[f886,f525])).

fof(f525,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(X8,k1_xboole_0,X9),X9)
      | k1_xboole_0 = X9 ) ),
    inference(backward_demodulation,[],[f114,f517])).

fof(f517,plain,(
    ! [X16] : k1_xboole_0 = k2_zfmisc_1(X16,k1_xboole_0) ),
    inference(forward_demodulation,[],[f349,f347])).

fof(f347,plain,(
    ! [X12] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X12) ),
    inference(resolution,[],[f104,f72])).

fof(f72,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f71,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f34,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f35,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(k1_xboole_0,X8,X9),X9)
      | k2_zfmisc_1(k1_xboole_0,X8) = X9 ) ),
    inference(resolution,[],[f30,f72])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f14,f17,f16,f15])).

fof(f15,plain,(
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
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,plain,(
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

fof(f349,plain,(
    ! [X15,X16] : k2_zfmisc_1(X16,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,X15) ),
    inference(resolution,[],[f104,f85])).

fof(f85,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X9,k1_xboole_0)) ),
    inference(resolution,[],[f44,f72])).

fof(f44,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f114,plain,(
    ! [X8,X9] :
      ( k2_zfmisc_1(X8,k1_xboole_0) = X9
      | r2_hidden(sK2(X8,k1_xboole_0,X9),X9) ) ),
    inference(resolution,[],[f31,f72])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f886,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f885])).

fof(f885,plain,
    ( spl7_6
  <=> ! [X9] : ~ r2_hidden(X9,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f906,plain,
    ( spl7_2
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f905])).

fof(f905,plain,
    ( $false
    | spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f892,f52])).

fof(f52,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f892,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(resolution,[],[f889,f525])).

fof(f889,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f888])).

fof(f888,plain,
    ( spl7_7
  <=> ! [X10] : ~ r2_hidden(X10,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f890,plain,
    ( spl7_6
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f883,f63,f888,f885])).

fof(f63,plain,
    ( spl7_5
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f883,plain,
    ( ! [X10,X9] :
        ( ~ r2_hidden(X10,sK1)
        | ~ r2_hidden(X9,sK0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f879,f72])).

fof(f879,plain,
    ( ! [X10,X9] :
        ( r2_hidden(k4_tarski(X9,X10),k1_xboole_0)
        | ~ r2_hidden(X10,sK1)
        | ~ r2_hidden(X9,sK0) )
    | ~ spl7_5 ),
    inference(superposition,[],[f42,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f42,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f875,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f874])).

fof(f874,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f57,f347])).

fof(f57,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f873,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f872])).

fof(f872,plain,
    ( $false
    | spl7_1 ),
    inference(trivial_inequality_removal,[],[f871])).

fof(f871,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl7_1 ),
    inference(superposition,[],[f49,f517])).

fof(f49,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl7_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f67,plain,
    ( spl7_5
    | spl7_4
    | spl7_2 ),
    inference(avatar_split_clause,[],[f22,f51,f59,f63])).

fof(f22,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
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

fof(f10,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f61,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f54,f59,f56])).

fof(f54,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f46,f51,f48])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:08 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.44  % (1898)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (1879)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (1886)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (1881)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (1893)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (1879)Refutation not found, incomplete strategy% (1879)------------------------------
% 0.21/0.50  % (1879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1879)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1879)Memory used [KB]: 10618
% 0.21/0.50  % (1879)Time elapsed: 0.079 s
% 0.21/0.50  % (1879)------------------------------
% 0.21/0.50  % (1879)------------------------------
% 0.21/0.50  % (1889)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (1889)Refutation not found, incomplete strategy% (1889)------------------------------
% 0.21/0.50  % (1889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1889)Memory used [KB]: 6012
% 0.21/0.50  % (1889)Time elapsed: 0.084 s
% 0.21/0.50  % (1889)------------------------------
% 0.21/0.50  % (1889)------------------------------
% 0.21/0.50  % (1875)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (1900)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (1883)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (1875)Refutation not found, incomplete strategy% (1875)------------------------------
% 0.21/0.50  % (1875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1875)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1875)Memory used [KB]: 6140
% 0.21/0.50  % (1875)Time elapsed: 0.090 s
% 0.21/0.50  % (1875)------------------------------
% 0.21/0.50  % (1875)------------------------------
% 0.21/0.50  % (1882)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (1880)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (1884)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (1899)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (1890)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (1890)Refutation not found, incomplete strategy% (1890)------------------------------
% 0.21/0.51  % (1890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1890)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1890)Memory used [KB]: 10618
% 0.21/0.51  % (1890)Time elapsed: 0.092 s
% 0.21/0.51  % (1890)------------------------------
% 0.21/0.51  % (1890)------------------------------
% 0.21/0.51  % (1892)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (1887)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (1891)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (1897)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (1894)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (1888)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (1901)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (1891)Refutation not found, incomplete strategy% (1891)------------------------------
% 0.21/0.53  % (1891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1891)Memory used [KB]: 6012
% 0.21/0.53  % (1891)Time elapsed: 0.003 s
% 0.21/0.53  % (1891)------------------------------
% 0.21/0.53  % (1891)------------------------------
% 0.21/0.53  % (1901)Refutation not found, incomplete strategy% (1901)------------------------------
% 0.21/0.53  % (1901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1901)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1901)Memory used [KB]: 10618
% 0.21/0.53  % (1901)Time elapsed: 0.111 s
% 0.21/0.53  % (1901)------------------------------
% 0.21/0.53  % (1901)------------------------------
% 0.21/0.54  % (1880)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f923,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f53,f61,f67,f873,f875,f890,f906,f922])).
% 0.21/0.54  fof(f922,plain,(
% 0.21/0.54    spl7_4 | ~spl7_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f921])).
% 0.21/0.54  fof(f921,plain,(
% 0.21/0.54    $false | (spl7_4 | ~spl7_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f908,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl7_4 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f908,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl7_6),
% 0.21/0.54    inference(resolution,[],[f886,f525])).
% 0.21/0.54  fof(f525,plain,(
% 0.21/0.54    ( ! [X8,X9] : (r2_hidden(sK2(X8,k1_xboole_0,X9),X9) | k1_xboole_0 = X9) )),
% 0.21/0.54    inference(backward_demodulation,[],[f114,f517])).
% 0.21/0.54  fof(f517,plain,(
% 0.21/0.54    ( ! [X16] : (k1_xboole_0 = k2_zfmisc_1(X16,k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f349,f347])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    ( ! [X12] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X12)) )),
% 0.21/0.54    inference(resolution,[],[f104,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f71,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0) | r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(superposition,[],[f34,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.21/0.54    inference(nnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(superposition,[],[f35,f25])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X8,X9] : (r2_hidden(sK2(k1_xboole_0,X8,X9),X9) | k2_zfmisc_1(k1_xboole_0,X8) = X9) )),
% 0.21/0.54    inference(resolution,[],[f30,f72])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f14,f17,f16,f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.54    inference(rectify,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    ( ! [X15,X16] : (k2_zfmisc_1(X16,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,X15)) )),
% 0.21/0.54    inference(resolution,[],[f104,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X8,X9] : (~r2_hidden(X8,k2_zfmisc_1(X9,k1_xboole_0))) )),
% 0.21/0.54    inference(resolution,[],[f44,f72])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X8,X9] : (k2_zfmisc_1(X8,k1_xboole_0) = X9 | r2_hidden(sK2(X8,k1_xboole_0,X9),X9)) )),
% 0.21/0.54    inference(resolution,[],[f31,f72])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f886,plain,(
% 0.21/0.54    ( ! [X9] : (~r2_hidden(X9,sK0)) ) | ~spl7_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f885])).
% 0.21/0.54  fof(f885,plain,(
% 0.21/0.54    spl7_6 <=> ! [X9] : ~r2_hidden(X9,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.54  fof(f906,plain,(
% 0.21/0.54    spl7_2 | ~spl7_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f905])).
% 0.21/0.54  fof(f905,plain,(
% 0.21/0.54    $false | (spl7_2 | ~spl7_7)),
% 0.21/0.54    inference(subsumption_resolution,[],[f892,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.54  fof(f892,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl7_7),
% 0.21/0.54    inference(resolution,[],[f889,f525])).
% 0.21/0.54  fof(f889,plain,(
% 0.21/0.54    ( ! [X10] : (~r2_hidden(X10,sK1)) ) | ~spl7_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f888])).
% 0.21/0.54  fof(f888,plain,(
% 0.21/0.54    spl7_7 <=> ! [X10] : ~r2_hidden(X10,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.54  fof(f890,plain,(
% 0.21/0.54    spl7_6 | spl7_7 | ~spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f883,f63,f888,f885])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl7_5 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.54  fof(f883,plain,(
% 0.21/0.54    ( ! [X10,X9] : (~r2_hidden(X10,sK1) | ~r2_hidden(X9,sK0)) ) | ~spl7_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f879,f72])).
% 0.21/0.54  fof(f879,plain,(
% 0.21/0.54    ( ! [X10,X9] : (r2_hidden(k4_tarski(X9,X10),k1_xboole_0) | ~r2_hidden(X10,sK1) | ~r2_hidden(X9,sK0)) ) | ~spl7_5),
% 0.21/0.54    inference(superposition,[],[f42,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f63])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f875,plain,(
% 0.21/0.54    spl7_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f874])).
% 0.21/0.54  fof(f874,plain,(
% 0.21/0.54    $false | spl7_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f57,f347])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl7_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    spl7_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f873,plain,(
% 0.21/0.54    spl7_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f872])).
% 0.21/0.54  fof(f872,plain,(
% 0.21/0.54    $false | spl7_1),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f871])).
% 0.21/0.54  fof(f871,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | spl7_1),
% 0.21/0.54    inference(superposition,[],[f49,f517])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    spl7_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl7_5 | spl7_4 | spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f22,f51,f59,f63])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(flattening,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,plain,(
% 0.21/0.54    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f5])).
% 0.21/0.54  fof(f5,conjecture,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ~spl7_3 | ~spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f54,f59,f56])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.54    inference(inner_rewriting,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f46,f51,f48])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.54    inference(inner_rewriting,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (1880)------------------------------
% 0.21/0.54  % (1880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1880)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (1880)Memory used [KB]: 11385
% 0.21/0.54  % (1880)Time elapsed: 0.132 s
% 0.21/0.54  % (1880)------------------------------
% 0.21/0.54  % (1880)------------------------------
% 0.21/0.54  % (1874)Success in time 0.185 s
%------------------------------------------------------------------------------
