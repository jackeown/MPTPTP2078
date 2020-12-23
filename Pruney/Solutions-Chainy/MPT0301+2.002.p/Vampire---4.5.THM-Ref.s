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
% DateTime   : Thu Dec  3 12:41:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 734 expanded)
%              Number of leaves         :   18 ( 227 expanded)
%              Depth                    :   21
%              Number of atoms          :  359 (3718 expanded)
%              Number of equality atoms :  126 ( 997 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f76,f404,f433,f442,f783,f1126])).

fof(f1126,plain,
    ( spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f1125])).

fof(f1125,plain,
    ( $false
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1106,f74])).

fof(f74,plain,
    ( k1_xboole_0 != sK0
    | spl8_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1106,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(superposition,[],[f310,f1093])).

fof(f1093,plain,
    ( ! [X78] : sK0 = k2_zfmisc_1(X78,sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f791,f438])).

fof(f438,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl8_4
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f791,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK3(X4,sK0,X5),X5)
        | k2_zfmisc_1(X4,sK0) = X5 )
    | ~ spl8_4 ),
    inference(resolution,[],[f438,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f24,f23,f22])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f310,plain,(
    ! [X23] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X23) ),
    inference(resolution,[],[f284,f123])).

fof(f123,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f122,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f122,plain,(
    ! [X2,X1] : ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f121,f86])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f121,plain,(
    ! [X2,X1] : ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))) ),
    inference(condensation,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))) ) ),
    inference(forward_demodulation,[],[f115,f30])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0))
      | ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))) ) ),
    inference(superposition,[],[f104,f29])).

fof(f104,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X5,k5_xboole_0(X6,k3_xboole_0(X6,X3)))
      | ~ r2_hidden(X5,k5_xboole_0(X3,k3_xboole_0(X4,X3))) ) ),
    inference(superposition,[],[f94,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r2_hidden(X0,k5_xboole_0(X3,k3_xboole_0(X3,X1))) ) ),
    inference(resolution,[],[f56,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (18593)Termination reason: Refutation not found, incomplete strategy
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

% (18593)Memory used [KB]: 6140
% (18593)Time elapsed: 0.035 s
% (18593)------------------------------
% (18593)------------------------------
fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f284,plain,(
    ! [X30,X31] :
      ( r2_hidden(sK3(k1_xboole_0,X30,X31),X31)
      | k2_zfmisc_1(k1_xboole_0,X30) = X31 ) ),
    inference(resolution,[],[f44,f123])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f783,plain,
    ( spl8_2
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f782])).

fof(f782,plain,
    ( $false
    | spl8_2
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f763,f69])).

fof(f69,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f763,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_5 ),
    inference(superposition,[],[f387,f750])).

fof(f750,plain,
    ( ! [X78] : sK1 = k2_zfmisc_1(sK1,X78)
    | ~ spl8_5 ),
    inference(resolution,[],[f447,f441])).

fof(f441,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl8_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f447,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK3(sK1,X8,X9),X9)
        | k2_zfmisc_1(sK1,X8) = X9 )
    | ~ spl8_5 ),
    inference(resolution,[],[f441,f44])).

fof(f387,plain,(
    ! [X25] : k1_xboole_0 = k2_zfmisc_1(X25,k1_xboole_0) ),
    inference(forward_demodulation,[],[f311,f310])).

fof(f311,plain,(
    ! [X24,X25] : k2_zfmisc_1(k1_xboole_0,X24) = k2_zfmisc_1(X25,k1_xboole_0) ),
    inference(resolution,[],[f284,f130])).

fof(f130,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(X5,k1_xboole_0)) ),
    inference(resolution,[],[f123,f60])).

fof(f60,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f442,plain,
    ( spl8_4
    | spl8_5
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f435,f63,f440,f437])).

fof(f63,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f435,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f434,f123])).

fof(f434,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f58,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f58,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f433,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f431,f310])).

fof(f431,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl8_1
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f65,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f65,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f404,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(trivial_inequality_removal,[],[f402])).

fof(f402,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f77,f387])).

fof(f77,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f65,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f76,plain,
    ( spl8_1
    | spl8_3
    | spl8_2 ),
    inference(avatar_split_clause,[],[f26,f67,f72,f63])).

fof(f26,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
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

fof(f12,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f75,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f27,f72,f63])).

fof(f27,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f28,f67,f63])).

fof(f28,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (18527)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (18527)Refutation not found, incomplete strategy% (18527)------------------------------
% 0.22/0.47  % (18527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (18527)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (18527)Memory used [KB]: 6268
% 0.22/0.47  % (18527)Time elapsed: 0.072 s
% 0.22/0.47  % (18527)------------------------------
% 0.22/0.47  % (18527)------------------------------
% 0.22/0.48  % (18545)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.48  % (18534)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.48  % (18526)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.48  % (18551)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.48  % (18534)Refutation not found, incomplete strategy% (18534)------------------------------
% 0.22/0.48  % (18534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (18534)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (18534)Memory used [KB]: 10618
% 0.22/0.48  % (18534)Time elapsed: 0.083 s
% 0.22/0.48  % (18534)------------------------------
% 0.22/0.48  % (18534)------------------------------
% 0.22/0.49  % (18530)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.49  % (18528)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.49  % (18537)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.49  % (18535)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (18525)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (18525)Refutation not found, incomplete strategy% (18525)------------------------------
% 0.22/0.50  % (18525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18525)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18525)Memory used [KB]: 10618
% 0.22/0.50  % (18525)Time elapsed: 0.095 s
% 0.22/0.50  % (18525)------------------------------
% 0.22/0.50  % (18525)------------------------------
% 0.22/0.50  % (18545)Refutation not found, incomplete strategy% (18545)------------------------------
% 0.22/0.50  % (18545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18545)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18545)Memory used [KB]: 10746
% 0.22/0.50  % (18545)Time elapsed: 0.084 s
% 0.22/0.50  % (18545)------------------------------
% 0.22/0.50  % (18545)------------------------------
% 0.22/0.51  % (18523)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (18523)Refutation not found, incomplete strategy% (18523)------------------------------
% 0.22/0.51  % (18523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18523)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18523)Memory used [KB]: 1663
% 0.22/0.51  % (18523)Time elapsed: 0.104 s
% 0.22/0.51  % (18523)------------------------------
% 0.22/0.51  % (18523)------------------------------
% 0.22/0.51  % (18547)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (18524)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (18544)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (18550)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (18529)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (18531)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (18552)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (18543)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (18531)Refutation not found, incomplete strategy% (18531)------------------------------
% 0.22/0.52  % (18531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18531)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18531)Memory used [KB]: 10618
% 0.22/0.52  % (18531)Time elapsed: 0.107 s
% 0.22/0.52  % (18531)------------------------------
% 0.22/0.52  % (18531)------------------------------
% 0.22/0.52  % (18532)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (18546)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (18532)Refutation not found, incomplete strategy% (18532)------------------------------
% 0.22/0.52  % (18532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18543)Refutation not found, incomplete strategy% (18543)------------------------------
% 0.22/0.53  % (18543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18538)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (18539)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (18540)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (18533)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (18538)Refutation not found, incomplete strategy% (18538)------------------------------
% 0.22/0.53  % (18538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18533)Refutation not found, incomplete strategy% (18533)------------------------------
% 0.22/0.53  % (18533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18538)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18538)Memory used [KB]: 6140
% 0.22/0.53  % (18538)Time elapsed: 0.004 s
% 0.22/0.53  % (18538)------------------------------
% 0.22/0.53  % (18538)------------------------------
% 0.22/0.54  % (18536)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (18548)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (18532)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18532)Memory used [KB]: 10618
% 0.22/0.54  % (18532)Time elapsed: 0.119 s
% 0.22/0.54  % (18532)------------------------------
% 0.22/0.54  % (18532)------------------------------
% 0.22/0.54  % (18543)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18543)Memory used [KB]: 10746
% 0.22/0.54  % (18543)Time elapsed: 0.125 s
% 0.22/0.54  % (18543)------------------------------
% 0.22/0.54  % (18543)------------------------------
% 0.22/0.55  % (18533)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18533)Memory used [KB]: 10618
% 0.22/0.55  % (18533)Time elapsed: 0.137 s
% 0.22/0.55  % (18533)------------------------------
% 0.22/0.55  % (18533)------------------------------
% 0.22/0.55  % (18542)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (18548)Refutation not found, incomplete strategy% (18548)------------------------------
% 0.22/0.55  % (18548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18548)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18548)Memory used [KB]: 6268
% 0.22/0.55  % (18548)Time elapsed: 0.136 s
% 0.22/0.55  % (18548)------------------------------
% 0.22/0.55  % (18548)------------------------------
% 0.22/0.55  % (18549)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (18540)Refutation not found, incomplete strategy% (18540)------------------------------
% 0.22/0.55  % (18540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18540)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18540)Memory used [KB]: 10618
% 0.22/0.55  % (18540)Time elapsed: 0.148 s
% 0.22/0.55  % (18540)------------------------------
% 0.22/0.55  % (18540)------------------------------
% 0.22/0.56  % (18541)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (18526)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (18593)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.22/0.56  % (18593)Refutation not found, incomplete strategy% (18593)------------------------------
% 0.22/0.56  % (18593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f1132,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f70,f75,f76,f404,f433,f442,f783,f1126])).
% 0.22/0.57  fof(f1126,plain,(
% 0.22/0.57    spl8_3 | ~spl8_4),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f1125])).
% 0.22/0.57  fof(f1125,plain,(
% 0.22/0.57    $false | (spl8_3 | ~spl8_4)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1106,f74])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    k1_xboole_0 != sK0 | spl8_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f72])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    spl8_3 <=> k1_xboole_0 = sK0),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.57  fof(f1106,plain,(
% 0.22/0.57    k1_xboole_0 = sK0 | ~spl8_4),
% 0.22/0.57    inference(superposition,[],[f310,f1093])).
% 0.22/0.57  fof(f1093,plain,(
% 0.22/0.57    ( ! [X78] : (sK0 = k2_zfmisc_1(X78,sK0)) ) | ~spl8_4),
% 0.22/0.57    inference(resolution,[],[f791,f438])).
% 0.22/0.57  fof(f438,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f437])).
% 0.22/0.57  fof(f437,plain,(
% 0.22/0.57    spl8_4 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.57  fof(f791,plain,(
% 0.22/0.57    ( ! [X4,X5] : (r2_hidden(sK3(X4,sK0,X5),X5) | k2_zfmisc_1(X4,sK0) = X5) ) | ~spl8_4),
% 0.22/0.57    inference(resolution,[],[f438,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f24,f23,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.57    inference(rectify,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.57  fof(f310,plain,(
% 0.22/0.57    ( ! [X23] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X23)) )),
% 0.22/0.57    inference(resolution,[],[f284,f123])).
% 0.22/0.57  fof(f123,plain,(
% 0.22/0.57    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f122,f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    ( ! [X2,X1] : (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f121,f86])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.57    inference(superposition,[],[f32,f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.57  fof(f121,plain,(
% 0.22/0.57    ( ! [X2,X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0)))) )),
% 0.22/0.57    inference(condensation,[],[f120])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0)))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f115,f30])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0)) | ~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0)))) )),
% 0.22/0.57    inference(superposition,[],[f104,f29])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    ( ! [X6,X4,X5,X3] : (~r2_hidden(X5,k5_xboole_0(X6,k3_xboole_0(X6,X3))) | ~r2_hidden(X5,k5_xboole_0(X3,k3_xboole_0(X4,X3)))) )),
% 0.22/0.57    inference(superposition,[],[f94,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r2_hidden(X0,k5_xboole_0(X3,k3_xboole_0(X3,X1)))) )),
% 0.22/0.57    inference(resolution,[],[f56,f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.22/0.57    inference(equality_resolution,[],[f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.22/0.57    inference(definition_unfolding,[],[f35,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  % (18593)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(rectify,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(flattening,[],[f15])).
% 0.22/0.57  
% 0.22/0.57  % (18593)Memory used [KB]: 6140
% 0.22/0.57  % (18593)Time elapsed: 0.035 s
% 0.22/0.57  % (18593)------------------------------
% 0.22/0.57  % (18593)------------------------------
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.22/0.57    inference(equality_resolution,[],[f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.22/0.57    inference(definition_unfolding,[],[f34,f33])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f284,plain,(
% 0.22/0.57    ( ! [X30,X31] : (r2_hidden(sK3(k1_xboole_0,X30,X31),X31) | k2_zfmisc_1(k1_xboole_0,X30) = X31) )),
% 0.22/0.57    inference(resolution,[],[f44,f123])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f783,plain,(
% 0.22/0.57    spl8_2 | ~spl8_5),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f782])).
% 0.22/0.57  fof(f782,plain,(
% 0.22/0.57    $false | (spl8_2 | ~spl8_5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f763,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | spl8_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    spl8_2 <=> k1_xboole_0 = sK1),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.57  fof(f763,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | ~spl8_5),
% 0.22/0.57    inference(superposition,[],[f387,f750])).
% 0.22/0.57  fof(f750,plain,(
% 0.22/0.57    ( ! [X78] : (sK1 = k2_zfmisc_1(sK1,X78)) ) | ~spl8_5),
% 0.22/0.57    inference(resolution,[],[f447,f441])).
% 0.22/0.57  fof(f441,plain,(
% 0.22/0.57    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f440])).
% 0.22/0.57  fof(f440,plain,(
% 0.22/0.57    spl8_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.57  fof(f447,plain,(
% 0.22/0.57    ( ! [X8,X9] : (r2_hidden(sK3(sK1,X8,X9),X9) | k2_zfmisc_1(sK1,X8) = X9) ) | ~spl8_5),
% 0.22/0.57    inference(resolution,[],[f441,f44])).
% 0.22/0.57  fof(f387,plain,(
% 0.22/0.57    ( ! [X25] : (k1_xboole_0 = k2_zfmisc_1(X25,k1_xboole_0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f311,f310])).
% 0.22/0.57  fof(f311,plain,(
% 0.22/0.57    ( ! [X24,X25] : (k2_zfmisc_1(k1_xboole_0,X24) = k2_zfmisc_1(X25,k1_xboole_0)) )),
% 0.22/0.57    inference(resolution,[],[f284,f130])).
% 0.22/0.57  fof(f130,plain,(
% 0.22/0.57    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(X5,k1_xboole_0))) )),
% 0.22/0.57    inference(resolution,[],[f123,f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f442,plain,(
% 0.22/0.57    spl8_4 | spl8_5 | ~spl8_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f435,f63,f440,f437])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.57  fof(f435,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f434,f123])).
% 0.22/0.57  fof(f434,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_1),
% 0.22/0.57    inference(superposition,[],[f58,f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f63])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.57    inference(equality_resolution,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f433,plain,(
% 0.22/0.57    spl8_1 | ~spl8_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f432])).
% 0.22/0.57  fof(f432,plain,(
% 0.22/0.57    $false | (spl8_1 | ~spl8_3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f431,f310])).
% 0.22/0.57  fof(f431,plain,(
% 0.22/0.57    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl8_1 | ~spl8_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f65,f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    k1_xboole_0 = sK0 | ~spl8_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f72])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl8_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f63])).
% 0.22/0.57  fof(f404,plain,(
% 0.22/0.57    spl8_1 | ~spl8_2),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f403])).
% 0.22/0.57  fof(f403,plain,(
% 0.22/0.57    $false | (spl8_1 | ~spl8_2)),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f402])).
% 0.22/0.57  fof(f402,plain,(
% 0.22/0.57    k1_xboole_0 != k1_xboole_0 | (spl8_1 | ~spl8_2)),
% 0.22/0.57    inference(superposition,[],[f77,f387])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl8_1 | ~spl8_2)),
% 0.22/0.57    inference(forward_demodulation,[],[f65,f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | ~spl8_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f67])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    spl8_1 | spl8_3 | spl8_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f26,f67,f72,f63])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.57    inference(flattening,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    inference(negated_conjecture,[],[f8])).
% 0.22/0.57  fof(f8,conjecture,(
% 0.22/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    ~spl8_1 | ~spl8_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f27,f72,f63])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ~spl8_1 | ~spl8_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f28,f67,f63])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (18526)------------------------------
% 0.22/0.57  % (18526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (18526)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (18526)Memory used [KB]: 11513
% 0.22/0.57  % (18526)Time elapsed: 0.173 s
% 0.22/0.57  % (18526)------------------------------
% 0.22/0.57  % (18526)------------------------------
% 0.22/0.57  % (18522)Success in time 0.203 s
%------------------------------------------------------------------------------
