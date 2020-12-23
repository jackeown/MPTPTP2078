%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 330 expanded)
%              Number of leaves         :   14 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  248 (1784 expanded)
%              Number of equality atoms :  114 ( 690 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f55,f61,f143,f258,f265,f272])).

fof(f272,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl7_9 ),
    inference(resolution,[],[f257,f62])).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f39,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f39,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f257,plain,
    ( ! [X12,X11] : r2_hidden(k4_tarski(sK2(X11,k1_xboole_0,sK0),sK2(X12,k1_xboole_0,sK1)),k1_xboole_0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl7_9
  <=> ! [X11,X12] : r2_hidden(k4_tarski(sK2(X11,k1_xboole_0,sK0),sK2(X12,k1_xboole_0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f265,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl7_1 ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl7_1 ),
    inference(superposition,[],[f43,f155])).

fof(f155,plain,(
    ! [X9] : k1_xboole_0 = k2_zfmisc_1(X9,k1_xboole_0) ),
    inference(resolution,[],[f81,f62])).

fof(f81,plain,(
    ! [X19,X17,X18] :
      ( r2_hidden(sK6(X18,X19,sK2(k1_xboole_0,X17,k2_zfmisc_1(X18,X19))),X19)
      | k1_xboole_0 = k2_zfmisc_1(X18,X19) ) ),
    inference(forward_demodulation,[],[f77,f73])).

fof(f73,plain,(
    ! [X7] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X7) ),
    inference(resolution,[],[f66,f62])).

fof(f66,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK2(k1_xboole_0,X9,X10),X10)
      | k2_zfmisc_1(k1_xboole_0,X9) = X10 ) ),
    inference(resolution,[],[f27,f62])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f12,f15,f14,f13])).

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f77,plain,(
    ! [X19,X17,X18] :
      ( k2_zfmisc_1(k1_xboole_0,X17) = k2_zfmisc_1(X18,X19)
      | r2_hidden(sK6(X18,X19,sK2(k1_xboole_0,X17,k2_zfmisc_1(X18,X19))),X19) ) ),
    inference(resolution,[],[f66,f37])).

fof(f37,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK6(X0,X1,X8),X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl7_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f258,plain,
    ( spl7_4
    | spl7_2
    | spl7_9
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f252,f57,f256,f45,f53])).

fof(f53,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f45,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f57,plain,
    ( spl7_5
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f252,plain,
    ( ! [X12,X11] :
        ( r2_hidden(k4_tarski(sK2(X11,k1_xboole_0,sK0),sK2(X12,k1_xboole_0,sK1)),k1_xboole_0)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_5 ),
    inference(superposition,[],[f186,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f186,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(k4_tarski(sK2(X4,k1_xboole_0,X5),sK2(X6,k1_xboole_0,X7)),k2_zfmisc_1(X5,X7))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f176,f175])).

fof(f175,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK2(X9,k1_xboole_0,X10),X10)
      | k1_xboole_0 = X10 ) ),
    inference(forward_demodulation,[],[f170,f155])).

fof(f170,plain,(
    ! [X10,X9] :
      ( k2_zfmisc_1(X9,k1_xboole_0) = X10
      | r2_hidden(sK2(X9,k1_xboole_0,X10),X10) ) ),
    inference(resolution,[],[f28,f62])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X1,sK2(X2,k1_xboole_0,X0)),k2_zfmisc_1(X3,X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f175,f35])).

fof(f35,plain,(
    ! [X0,X10,X1,X9] :
      ( ~ r2_hidden(X10,X1)
      | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl7_3 ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl7_3 ),
    inference(superposition,[],[f51,f73])).

fof(f51,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl7_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f61,plain,
    ( spl7_5
    | spl7_4
    | spl7_2 ),
    inference(avatar_split_clause,[],[f19,f45,f53,f57])).

fof(f19,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
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

fof(f8,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f55,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f48,f53,f50])).

fof(f48,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f40,f45,f42])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (13094)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (13091)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (13092)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (13102)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (13099)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (13092)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (13100)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f278,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f47,f55,f61,f143,f258,f265,f272])).
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    ~spl7_9),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f267])).
% 0.20/0.52  fof(f267,plain,(
% 0.20/0.52    $false | ~spl7_9),
% 0.20/0.52    inference(resolution,[],[f257,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f39,f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    ( ! [X12,X11] : (r2_hidden(k4_tarski(sK2(X11,k1_xboole_0,sK0),sK2(X12,k1_xboole_0,sK1)),k1_xboole_0)) ) | ~spl7_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f256])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    spl7_9 <=> ! [X11,X12] : r2_hidden(k4_tarski(sK2(X11,k1_xboole_0,sK0),sK2(X12,k1_xboole_0,sK1)),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    spl7_1),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f264])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    $false | spl7_1),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f261])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | spl7_1),
% 0.20/0.53    inference(superposition,[],[f43,f155])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(X9,k1_xboole_0)) )),
% 0.20/0.53    inference(resolution,[],[f81,f62])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X19,X17,X18] : (r2_hidden(sK6(X18,X19,sK2(k1_xboole_0,X17,k2_zfmisc_1(X18,X19))),X19) | k1_xboole_0 = k2_zfmisc_1(X18,X19)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f77,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X7] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X7)) )),
% 0.20/0.53    inference(resolution,[],[f66,f62])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X10,X9] : (r2_hidden(sK2(k1_xboole_0,X9,X10),X10) | k2_zfmisc_1(k1_xboole_0,X9) = X10) )),
% 0.20/0.53    inference(resolution,[],[f27,f62])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f12,f15,f14,f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X19,X17,X18] : (k2_zfmisc_1(k1_xboole_0,X17) = k2_zfmisc_1(X18,X19) | r2_hidden(sK6(X18,X19,sK2(k1_xboole_0,X17,k2_zfmisc_1(X18,X19))),X19)) )),
% 0.20/0.53    inference(resolution,[],[f66,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X8,X1] : (~r2_hidden(X8,k2_zfmisc_1(X0,X1)) | r2_hidden(sK6(X0,X1,X8),X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl7_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    spl7_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    spl7_4 | spl7_2 | spl7_9 | ~spl7_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f252,f57,f256,f45,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    spl7_4 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    spl7_2 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    spl7_5 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    ( ! [X12,X11] : (r2_hidden(k4_tarski(sK2(X11,k1_xboole_0,sK0),sK2(X12,k1_xboole_0,sK1)),k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_5),
% 0.20/0.53    inference(superposition,[],[f186,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl7_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f57])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    ( ! [X6,X4,X7,X5] : (r2_hidden(k4_tarski(sK2(X4,k1_xboole_0,X5),sK2(X6,k1_xboole_0,X7)),k2_zfmisc_1(X5,X7)) | k1_xboole_0 = X7 | k1_xboole_0 = X5) )),
% 0.20/0.53    inference(resolution,[],[f176,f175])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    ( ! [X10,X9] : (r2_hidden(sK2(X9,k1_xboole_0,X10),X10) | k1_xboole_0 = X10) )),
% 0.20/0.53    inference(forward_demodulation,[],[f170,f155])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    ( ! [X10,X9] : (k2_zfmisc_1(X9,k1_xboole_0) = X10 | r2_hidden(sK2(X9,k1_xboole_0,X10),X10)) )),
% 0.20/0.53    inference(resolution,[],[f28,f62])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X1,sK2(X2,k1_xboole_0,X0)),k2_zfmisc_1(X3,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(resolution,[],[f175,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X10,X1,X9] : (~r2_hidden(X10,X1) | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X9,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    spl7_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    $false | spl7_3),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f139])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | spl7_3),
% 0.20/0.53    inference(superposition,[],[f51,f73])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl7_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    spl7_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    spl7_5 | spl7_4 | spl7_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f19,f45,f53,f57])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(flattening,[],[f7])).
% 0.20/0.53  fof(f7,plain,(
% 0.20/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    inference(negated_conjecture,[],[f4])).
% 0.20/0.53  fof(f4,conjecture,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ~spl7_3 | ~spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f48,f53,f50])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.53    inference(inner_rewriting,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f40,f45,f42])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.53    inference(inner_rewriting,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (13092)------------------------------
% 0.20/0.53  % (13092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13092)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (13092)Memory used [KB]: 10874
% 0.20/0.53  % (13092)Time elapsed: 0.077 s
% 0.20/0.53  % (13092)------------------------------
% 0.20/0.53  % (13092)------------------------------
% 0.20/0.53  % (13085)Success in time 0.166 s
%------------------------------------------------------------------------------
