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
% DateTime   : Thu Dec  3 12:41:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 340 expanded)
%              Number of leaves         :   20 ( 126 expanded)
%              Depth                    :   15
%              Number of atoms          :  317 (1807 expanded)
%              Number of equality atoms :  110 ( 579 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f70,f76,f91,f96,f478,f480,f495,f509,f523])).

fof(f523,plain,
    ( spl8_4
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl8_4
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f513,f69])).

fof(f69,plain,
    ( k1_xboole_0 != sK0
    | spl8_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f513,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(resolution,[],[f491,f333])).

fof(f333,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK3(X4,k1_xboole_0,X5),X5)
        | k1_xboole_0 = X5 )
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f117,f322])).

fof(f322,plain,
    ( ! [X8] : k1_xboole_0 = k2_zfmisc_1(X8,k1_xboole_0)
    | ~ spl8_7 ),
    inference(resolution,[],[f277,f98])).

fof(f98,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ spl8_7 ),
    inference(resolution,[],[f90,f53])).

fof(f53,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f22,f25,f24,f23])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f90,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_7
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f277,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK3(k1_xboole_0,X4,X5),X5)
        | k1_xboole_0 = X5 )
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f111,f275])).

fof(f275,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f256,f129])).

fof(f129,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl8_7 ),
    inference(resolution,[],[f93,f90])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f37,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f256,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl8_7 ),
    inference(superposition,[],[f171,f32])).

fof(f171,plain,
    ( ! [X6,X7,X5] :
        ( k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X5,X6),X7)
        | ~ r1_xboole_0(X5,X6) )
    | ~ spl8_7 ),
    inference(resolution,[],[f110,f90])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(k3_xboole_0(X0,X1),X2,X3),X3)
      | k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = X3
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(k1_xboole_0,X4) = X5
        | r2_hidden(sK3(k1_xboole_0,X4,X5),X5) )
    | ~ spl8_7 ),
    inference(resolution,[],[f43,f90])).

fof(f117,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(X4,k1_xboole_0) = X5
        | r2_hidden(sK3(X4,k1_xboole_0,X5),X5) )
    | ~ spl8_7 ),
    inference(resolution,[],[f44,f90])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f491,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f490])).

fof(f490,plain,
    ( spl8_8
  <=> ! [X9] : ~ r2_hidden(X9,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f509,plain,
    ( spl8_2
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | spl8_2
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f499,f61])).

fof(f61,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f499,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(resolution,[],[f494,f333])).

fof(f494,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl8_9
  <=> ! [X10] : ~ r2_hidden(X10,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f495,plain,
    ( spl8_8
    | spl8_9
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f488,f89,f72,f493,f490])).

fof(f72,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f488,plain,
    ( ! [X10,X9] :
        ( ~ r2_hidden(X10,sK1)
        | ~ r2_hidden(X9,sK0) )
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f484,f90])).

fof(f484,plain,
    ( ! [X10,X9] :
        ( r2_hidden(k4_tarski(X9,X10),k1_xboole_0)
        | ~ r2_hidden(X10,sK1)
        | ~ r2_hidden(X9,sK0) )
    | ~ spl8_5 ),
    inference(superposition,[],[f51,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f51,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f480,plain,
    ( spl8_3
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl8_3
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f66,f275])).

fof(f66,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl8_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f478,plain,
    ( spl8_1
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | spl8_1
    | ~ spl8_7 ),
    inference(trivial_inequality_removal,[],[f476])).

fof(f476,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_1
    | ~ spl8_7 ),
    inference(superposition,[],[f58,f322])).

fof(f58,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f96,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl8_6 ),
    inference(resolution,[],[f87,f82])).

fof(f82,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f80,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f80,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f32])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f87,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_6
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f91,plain,
    ( spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f84,f89,f86])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f38,f32])).

fof(f76,plain,
    ( spl8_5
    | spl8_4
    | spl8_2 ),
    inference(avatar_split_clause,[],[f29,f60,f68,f72])).

fof(f29,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
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

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f70,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f63,f68,f65])).

fof(f63,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f55,f60,f57])).

fof(f55,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:58:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (12723)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (12719)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (12730)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (12730)Refutation not found, incomplete strategy% (12730)------------------------------
% 0.22/0.49  % (12730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12730)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12730)Memory used [KB]: 10618
% 0.22/0.49  % (12730)Time elapsed: 0.071 s
% 0.22/0.49  % (12730)------------------------------
% 0.22/0.49  % (12730)------------------------------
% 0.22/0.49  % (12733)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (12724)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (12732)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (12734)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (12731)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12729)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (12729)Refutation not found, incomplete strategy% (12729)------------------------------
% 0.22/0.50  % (12729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12729)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12729)Memory used [KB]: 6012
% 0.22/0.50  % (12729)Time elapsed: 0.088 s
% 0.22/0.50  % (12729)------------------------------
% 0.22/0.50  % (12729)------------------------------
% 0.22/0.50  % (12731)Refutation not found, incomplete strategy% (12731)------------------------------
% 0.22/0.50  % (12731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12731)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12731)Memory used [KB]: 6140
% 0.22/0.50  % (12731)Time elapsed: 0.078 s
% 0.22/0.50  % (12731)------------------------------
% 0.22/0.50  % (12731)------------------------------
% 0.22/0.50  % (12720)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12719)Refutation not found, incomplete strategy% (12719)------------------------------
% 0.22/0.50  % (12719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12719)Memory used [KB]: 6140
% 0.22/0.50  % (12719)Time elapsed: 0.091 s
% 0.22/0.50  % (12719)------------------------------
% 0.22/0.50  % (12719)------------------------------
% 0.22/0.50  % (12720)Refutation not found, incomplete strategy% (12720)------------------------------
% 0.22/0.50  % (12720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12720)Memory used [KB]: 10618
% 0.22/0.50  % (12720)Time elapsed: 0.093 s
% 0.22/0.50  % (12720)------------------------------
% 0.22/0.50  % (12720)------------------------------
% 0.22/0.50  % (12725)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (12721)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (12737)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (12727)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (12726)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (12735)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (12739)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (12739)Refutation not found, incomplete strategy% (12739)------------------------------
% 0.22/0.51  % (12739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12739)Memory used [KB]: 10618
% 0.22/0.51  % (12739)Time elapsed: 0.105 s
% 0.22/0.51  % (12739)------------------------------
% 0.22/0.51  % (12739)------------------------------
% 0.22/0.51  % (12722)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (12722)Refutation not found, incomplete strategy% (12722)------------------------------
% 0.22/0.52  % (12722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12722)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12722)Memory used [KB]: 10618
% 0.22/0.52  % (12722)Time elapsed: 0.105 s
% 0.22/0.52  % (12722)------------------------------
% 0.22/0.52  % (12722)------------------------------
% 0.22/0.52  % (12728)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (12738)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (12736)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (12721)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f524,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f62,f70,f76,f91,f96,f478,f480,f495,f509,f523])).
% 0.22/0.53  fof(f523,plain,(
% 0.22/0.53    spl8_4 | ~spl8_7 | ~spl8_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f522])).
% 0.22/0.53  fof(f522,plain,(
% 0.22/0.53    $false | (spl8_4 | ~spl8_7 | ~spl8_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f513,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    k1_xboole_0 != sK0 | spl8_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl8_4 <=> k1_xboole_0 = sK0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.53  fof(f513,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | (~spl8_7 | ~spl8_8)),
% 0.22/0.53    inference(resolution,[],[f491,f333])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    ( ! [X4,X5] : (r2_hidden(sK3(X4,k1_xboole_0,X5),X5) | k1_xboole_0 = X5) ) | ~spl8_7),
% 0.22/0.53    inference(backward_demodulation,[],[f117,f322])).
% 0.22/0.53  fof(f322,plain,(
% 0.22/0.53    ( ! [X8] : (k1_xboole_0 = k2_zfmisc_1(X8,k1_xboole_0)) ) | ~spl8_7),
% 0.22/0.53    inference(resolution,[],[f277,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) ) | ~spl8_7),
% 0.22/0.53    inference(resolution,[],[f90,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f22,f25,f24,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl8_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl8_7 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    ( ! [X4,X5] : (r2_hidden(sK3(k1_xboole_0,X4,X5),X5) | k1_xboole_0 = X5) ) | ~spl8_7),
% 0.22/0.53    inference(backward_demodulation,[],[f111,f275])).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl8_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f256,f129])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl8_7),
% 0.22/0.53    inference(resolution,[],[f93,f90])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0) | r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f37,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) | ~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl8_7),
% 0.22/0.53    inference(superposition,[],[f171,f32])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X5,X6),X7) | ~r1_xboole_0(X5,X6)) ) | ~spl8_7),
% 0.22/0.53    inference(resolution,[],[f110,f90])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(k3_xboole_0(X0,X1),X2,X3),X3) | k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = X3 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f43,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X4,X5] : (k2_zfmisc_1(k1_xboole_0,X4) = X5 | r2_hidden(sK3(k1_xboole_0,X4,X5),X5)) ) | ~spl8_7),
% 0.22/0.53    inference(resolution,[],[f43,f90])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X4,X5] : (k2_zfmisc_1(X4,k1_xboole_0) = X5 | r2_hidden(sK3(X4,k1_xboole_0,X5),X5)) ) | ~spl8_7),
% 0.22/0.53    inference(resolution,[],[f44,f90])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f491,plain,(
% 0.22/0.53    ( ! [X9] : (~r2_hidden(X9,sK0)) ) | ~spl8_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f490])).
% 0.22/0.53  fof(f490,plain,(
% 0.22/0.53    spl8_8 <=> ! [X9] : ~r2_hidden(X9,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.53  fof(f509,plain,(
% 0.22/0.53    spl8_2 | ~spl8_7 | ~spl8_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f508])).
% 0.22/0.53  fof(f508,plain,(
% 0.22/0.53    $false | (spl8_2 | ~spl8_7 | ~spl8_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f499,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | spl8_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl8_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.53  fof(f499,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | (~spl8_7 | ~spl8_9)),
% 0.22/0.53    inference(resolution,[],[f494,f333])).
% 0.22/0.53  fof(f494,plain,(
% 0.22/0.53    ( ! [X10] : (~r2_hidden(X10,sK1)) ) | ~spl8_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f493])).
% 0.22/0.53  fof(f493,plain,(
% 0.22/0.53    spl8_9 <=> ! [X10] : ~r2_hidden(X10,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.53  fof(f495,plain,(
% 0.22/0.53    spl8_8 | spl8_9 | ~spl8_5 | ~spl8_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f488,f89,f72,f493,f490])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.53  fof(f488,plain,(
% 0.22/0.53    ( ! [X10,X9] : (~r2_hidden(X10,sK1) | ~r2_hidden(X9,sK0)) ) | (~spl8_5 | ~spl8_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f484,f90])).
% 0.22/0.53  fof(f484,plain,(
% 0.22/0.53    ( ! [X10,X9] : (r2_hidden(k4_tarski(X9,X10),k1_xboole_0) | ~r2_hidden(X10,sK1) | ~r2_hidden(X9,sK0)) ) | ~spl8_5),
% 0.22/0.53    inference(superposition,[],[f51,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f72])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f480,plain,(
% 0.22/0.53    spl8_3 | ~spl8_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f479])).
% 0.22/0.53  fof(f479,plain,(
% 0.22/0.53    $false | (spl8_3 | ~spl8_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f66,f275])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl8_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl8_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.53  fof(f478,plain,(
% 0.22/0.53    spl8_1 | ~spl8_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f477])).
% 0.22/0.53  fof(f477,plain,(
% 0.22/0.53    $false | (spl8_1 | ~spl8_7)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f476])).
% 0.22/0.53  fof(f476,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | (spl8_1 | ~spl8_7)),
% 0.22/0.53    inference(superposition,[],[f58,f322])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl8_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ~spl8_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    $false | ~spl8_6),
% 0.22/0.53    inference(resolution,[],[f87,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f80,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.53    inference(superposition,[],[f36,f32])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl8_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl8_6 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl8_6 | spl8_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f84,f89,f86])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f38,f32])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl8_5 | spl8_4 | spl8_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f60,f68,f72])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ~spl8_3 | ~spl8_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f63,f68,f65])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.22/0.53    inference(inner_rewriting,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ~spl8_1 | ~spl8_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f60,f57])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.22/0.53    inference(inner_rewriting,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (12721)------------------------------
% 0.22/0.53  % (12721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12721)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (12721)Memory used [KB]: 10874
% 0.22/0.53  % (12721)Time elapsed: 0.099 s
% 0.22/0.53  % (12721)------------------------------
% 0.22/0.53  % (12721)------------------------------
% 0.22/0.53  % (12718)Success in time 0.168 s
%------------------------------------------------------------------------------
