%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 405 expanded)
%              Number of leaves         :   17 ( 143 expanded)
%              Depth                    :   16
%              Number of atoms          :  273 (1906 expanded)
%              Number of equality atoms :  108 ( 591 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f57,f63,f374,f376,f387,f399,f411])).

fof(f411,plain,
    ( spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f403,f56])).

fof(f56,plain,
    ( k1_xboole_0 != sK0
    | spl8_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f403,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_6 ),
    inference(resolution,[],[f383,f244])).

fof(f244,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(X4,k1_xboole_0,X5),X5)
      | k1_xboole_0 = X5 ) ),
    inference(backward_demodulation,[],[f84,f233])).

fof(f233,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ),
    inference(resolution,[],[f194,f69])).

fof(f69,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(X5,k1_xboole_0)) ),
    inference(resolution,[],[f40,f65])).

fof(f65,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f28,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f40,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f194,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(k1_xboole_0,X4,X5),X5)
      | k1_xboole_0 = X5 ) ),
    inference(backward_demodulation,[],[f80,f190])).

fof(f190,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f174,f25])).

fof(f174,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f118,f26])).

fof(f118,plain,(
    ! [X6,X7,X5] :
      ( k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X5,X6),X7)
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(resolution,[],[f79,f65])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(k3_xboole_0(X0,X1),X2,X3),X3)
      | k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = X3
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X4,X5] :
      ( k2_zfmisc_1(k1_xboole_0,X4) = X5
      | r2_hidden(sK3(k1_xboole_0,X4,X5),X5) ) ),
    inference(resolution,[],[f33,f65])).

fof(f84,plain,(
    ! [X4,X5] :
      ( k2_zfmisc_1(X4,k1_xboole_0) = X5
      | r2_hidden(sK3(X4,k1_xboole_0,X5),X5) ) ),
    inference(resolution,[],[f34,f65])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f383,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl8_6
  <=> ! [X3] : ~ r2_hidden(X3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f399,plain,
    ( spl8_2
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f391,f48])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f391,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_7 ),
    inference(resolution,[],[f386,f244])).

fof(f386,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl8_7
  <=> ! [X4] : ~ r2_hidden(X4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f387,plain,
    ( spl8_6
    | spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f380,f59,f385,f382])).

fof(f59,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f380,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f378,f65])).

fof(f378,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k4_tarski(X3,X4),k1_xboole_0)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl8_5 ),
    inference(superposition,[],[f38,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f38,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f376,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f53,f190])).

fof(f53,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f374,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f369])).

fof(f369,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_1 ),
    inference(superposition,[],[f45,f233])).

fof(f45,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f63,plain,
    ( spl8_5
    | spl8_4
    | spl8_2 ),
    inference(avatar_split_clause,[],[f22,f47,f55,f59])).

fof(f22,plain,
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f57,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f50,f55,f52])).

fof(f50,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f42,f47,f44])).

fof(f42,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (4984)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (4987)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (4992)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (4984)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (4992)Refutation not found, incomplete strategy% (4992)------------------------------
% 0.21/0.48  % (4992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4992)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4992)Memory used [KB]: 6012
% 0.21/0.48  % (4992)Time elapsed: 0.063 s
% 0.21/0.48  % (4992)------------------------------
% 0.21/0.48  % (4992)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f49,f57,f63,f374,f376,f387,f399,f411])).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    spl8_4 | ~spl8_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    $false | (spl8_4 | ~spl8_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f403,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | spl8_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl8_4 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.48  fof(f403,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl8_6),
% 0.21/0.48    inference(resolution,[],[f383,f244])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    ( ! [X4,X5] : (r2_hidden(sK3(X4,k1_xboole_0,X5),X5) | k1_xboole_0 = X5) )),
% 0.21/0.48    inference(backward_demodulation,[],[f84,f233])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f194,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(X5,k1_xboole_0))) )),
% 0.21/0.48    inference(resolution,[],[f40,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f28,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f17,f20,f19,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.48    inference(rectify,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    ( ! [X4,X5] : (r2_hidden(sK3(k1_xboole_0,X4,X5),X5) | k1_xboole_0 = X5) )),
% 0.21/0.48    inference(backward_demodulation,[],[f80,f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f174,f25])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f118,f26])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X6,X7,X5] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X5,X6),X7) | ~r1_xboole_0(X5,X6)) )),
% 0.21/0.48    inference(resolution,[],[f79,f65])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(k3_xboole_0(X0,X1),X2,X3),X3) | k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = X3 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f33,f28])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X4,X5] : (k2_zfmisc_1(k1_xboole_0,X4) = X5 | r2_hidden(sK3(k1_xboole_0,X4,X5),X5)) )),
% 0.21/0.48    inference(resolution,[],[f33,f65])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X4,X5] : (k2_zfmisc_1(X4,k1_xboole_0) = X5 | r2_hidden(sK3(X4,k1_xboole_0,X5),X5)) )),
% 0.21/0.48    inference(resolution,[],[f34,f65])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(X3,sK0)) ) | ~spl8_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f382])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    spl8_6 <=> ! [X3] : ~r2_hidden(X3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    spl8_2 | ~spl8_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f398])).
% 0.21/0.48  fof(f398,plain,(
% 0.21/0.48    $false | (spl8_2 | ~spl8_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f391,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl8_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.48  fof(f391,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl8_7),
% 0.21/0.48    inference(resolution,[],[f386,f244])).
% 0.21/0.48  fof(f386,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(X4,sK1)) ) | ~spl8_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f385])).
% 0.21/0.48  fof(f385,plain,(
% 0.21/0.48    spl8_7 <=> ! [X4] : ~r2_hidden(X4,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.48  fof(f387,plain,(
% 0.21/0.48    spl8_6 | spl8_7 | ~spl8_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f380,f59,f385,f382])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~r2_hidden(X4,sK1) | ~r2_hidden(X3,sK0)) ) | ~spl8_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f378,f65])).
% 0.21/0.48  fof(f378,plain,(
% 0.21/0.48    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,X4),k1_xboole_0) | ~r2_hidden(X4,sK1) | ~r2_hidden(X3,sK0)) ) | ~spl8_5),
% 0.21/0.48    inference(superposition,[],[f38,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.49    inference(equality_resolution,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f376,plain,(
% 0.21/0.49    spl8_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f375])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    $false | spl8_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f53,f190])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl8_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl8_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    spl8_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f373])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    $false | spl8_1),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f369])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | spl8_1),
% 0.21/0.49    inference(superposition,[],[f45,f233])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl8_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl8_5 | spl8_4 | spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f47,f55,f59])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~spl8_3 | ~spl8_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f55,f52])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.49    inference(inner_rewriting,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ~spl8_1 | ~spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f47,f44])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.49    inference(inner_rewriting,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4984)------------------------------
% 0.21/0.49  % (4984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4984)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4984)Memory used [KB]: 10874
% 0.21/0.49  % (4984)Time elapsed: 0.059 s
% 0.21/0.49  % (4984)------------------------------
% 0.21/0.49  % (4984)------------------------------
% 0.21/0.49  % (4981)Success in time 0.127 s
%------------------------------------------------------------------------------
