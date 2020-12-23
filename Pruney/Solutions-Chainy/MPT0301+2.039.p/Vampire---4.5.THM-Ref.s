%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 171 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  276 ( 702 expanded)
%              Number of equality atoms :  104 ( 268 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f60,f66,f126,f128,f137,f147,f154])).

fof(f154,plain,
    ( spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f148,f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK0
    | spl8_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f148,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_6 ),
    inference(resolution,[],[f133,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f133,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_6
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f147,plain,
    ( spl8_2
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f141,f51])).

fof(f51,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f141,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_7 ),
    inference(resolution,[],[f136,f27])).

fof(f136,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_7
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f137,plain,
    ( spl8_6
    | spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f130,f62,f135,f132])).

fof(f62,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

% (17818)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f129,f84])).

fof(f84,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f81,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f37,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f39,f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_5 ),
    inference(superposition,[],[f41,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f41,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f17,f20,f19,f18])).

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f128,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f56,f103])).

fof(f103,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(resolution,[],[f92,f27])).

fof(f92,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(k1_xboole_0,X9)) ),
    inference(resolution,[],[f44,f84])).

fof(f44,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl8_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f126,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_1 ),
    inference(superposition,[],[f48,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f88,f27])).

fof(f88,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X9,k1_xboole_0)) ),
    inference(resolution,[],[f43,f84])).

fof(f43,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f66,plain,
    ( spl8_5
    | spl8_4
    | spl8_2 ),
    inference(avatar_split_clause,[],[f23,f50,f58,f62])).

fof(f23,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
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

fof(f11,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f60,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f53,f58,f55])).

fof(f53,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f45,f50,f47])).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (17814)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (17804)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (17820)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (17810)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (17810)Refutation not found, incomplete strategy% (17810)------------------------------
% 0.20/0.48  % (17810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17810)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17810)Memory used [KB]: 6012
% 0.20/0.48  % (17810)Time elapsed: 0.071 s
% 0.20/0.48  % (17810)------------------------------
% 0.20/0.48  % (17810)------------------------------
% 0.20/0.48  % (17819)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (17805)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (17809)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (17800)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (17800)Refutation not found, incomplete strategy% (17800)------------------------------
% 0.20/0.49  % (17800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17800)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17800)Memory used [KB]: 6140
% 0.20/0.49  % (17800)Time elapsed: 0.088 s
% 0.20/0.49  % (17800)------------------------------
% 0.20/0.49  % (17800)------------------------------
% 0.20/0.49  % (17813)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (17802)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (17820)Refutation not found, incomplete strategy% (17820)------------------------------
% 0.20/0.49  % (17820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17820)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17820)Memory used [KB]: 10618
% 0.20/0.49  % (17820)Time elapsed: 0.081 s
% 0.20/0.49  % (17820)------------------------------
% 0.20/0.49  % (17820)------------------------------
% 0.20/0.49  % (17802)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f52,f60,f66,f126,f128,f137,f147,f154])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    spl8_4 | ~spl8_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    $false | (spl8_4 | ~spl8_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f148,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    k1_xboole_0 != sK0 | spl8_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl8_4 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | ~spl8_6),
% 0.20/0.49    inference(resolution,[],[f133,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl8_6 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    spl8_2 | ~spl8_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f146])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    $false | (spl8_2 | ~spl8_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f141,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | spl8_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl8_2 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~spl8_7),
% 0.20/0.49    inference(resolution,[],[f136,f27])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl8_7 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl8_6 | spl8_7 | ~spl8_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f130,f62,f135,f132])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.49  % (17818)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f129,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f81,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.49    inference(superposition,[],[f37,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.49    inference(nnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.49    inference(superposition,[],[f39,f26])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_5),
% 0.20/0.49    inference(superposition,[],[f41,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f62])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.49    inference(equality_resolution,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f17,f20,f19,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.49    inference(rectify,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl8_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    $false | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f56,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 0.20/0.49    inference(resolution,[],[f92,f27])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X8,X9] : (~r2_hidden(X8,k2_zfmisc_1(k1_xboole_0,X9))) )),
% 0.20/0.49    inference(resolution,[],[f44,f84])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl8_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl8_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    spl8_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    $false | spl8_1),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f123])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | spl8_1),
% 0.20/0.49    inference(superposition,[],[f48,f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(resolution,[],[f88,f27])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X8,X9] : (~r2_hidden(X8,k2_zfmisc_1(X9,k1_xboole_0))) )),
% 0.20/0.49    inference(resolution,[],[f43,f84])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl8_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl8_5 | spl8_4 | spl8_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f50,f58,f62])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ~spl8_3 | ~spl8_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f53,f58,f55])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.49    inference(inner_rewriting,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ~spl8_1 | ~spl8_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f50,f47])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.49    inference(inner_rewriting,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (17802)------------------------------
% 0.20/0.49  % (17802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17802)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (17802)Memory used [KB]: 10618
% 0.20/0.49  % (17802)Time elapsed: 0.055 s
% 0.20/0.49  % (17802)------------------------------
% 0.20/0.49  % (17802)------------------------------
% 0.20/0.49  % (17812)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (17799)Success in time 0.138 s
%------------------------------------------------------------------------------
