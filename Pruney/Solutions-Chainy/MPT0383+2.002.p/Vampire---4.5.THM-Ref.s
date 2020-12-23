%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:41 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 200 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  406 (1121 expanded)
%              Number of equality atoms :   64 ( 220 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1071,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f81,f89,f441,f454,f470,f478,f1070])).

fof(f1070,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(avatar_contradiction_clause,[],[f1069])).

fof(f1069,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f67,f1068])).

fof(f1068,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl11_1
    | ~ spl11_3 ),
    inference(resolution,[],[f963,f63])).

fof(f63,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl11_1
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f963,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(X1,sK1))
        | ~ r2_hidden(X2,X0) )
    | ~ spl11_3 ),
    inference(superposition,[],[f538,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f538,plain,
    ( ! [X4,X5,X3] : ~ r2_hidden(X3,k3_xboole_0(X4,k2_zfmisc_1(X5,sK1)))
    | ~ spl11_3 ),
    inference(resolution,[],[f490,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f490,plain,
    ( ! [X14,X15] : ~ r2_hidden(X14,k2_zfmisc_1(X15,sK1))
    | ~ spl11_3 ),
    inference(resolution,[],[f481,f59])).

fof(f59,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK6(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2))
              & r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
                & r2_hidden(sK10(X0,X1,X8),X1)
                & r2_hidden(sK9(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f24,f27,f26,f25])).

fof(f25,plain,(
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
              ( k4_tarski(X4,X5) != sK6(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK6(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK6(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
        & r2_hidden(sK10(X0,X1,X8),X1)
        & r2_hidden(sK9(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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

fof(f481,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl11_3 ),
    inference(resolution,[],[f77,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f77,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl11_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f67,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl11_2
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f478,plain,
    ( ~ spl11_2
    | ~ spl11_7 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f67,f476])).

fof(f476,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl11_7 ),
    inference(resolution,[],[f440,f32])).

fof(f440,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl11_7
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f470,plain,
    ( ~ spl11_2
    | ~ spl11_1
    | spl11_8 ),
    inference(avatar_split_clause,[],[f468,f452,f62,f66])).

fof(f452,plain,
    ( spl11_8
  <=> r2_hidden(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f468,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl11_1
    | spl11_8 ),
    inference(resolution,[],[f467,f63])).

fof(f467,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK3,X0) )
    | spl11_8 ),
    inference(superposition,[],[f459,f38])).

fof(f459,plain,
    ( ! [X1] : ~ r2_hidden(sK3,k3_xboole_0(X1,k2_zfmisc_1(sK0,sK1)))
    | spl11_8 ),
    inference(resolution,[],[f453,f54])).

fof(f453,plain,
    ( ~ r2_hidden(sK3,k2_zfmisc_1(sK0,sK1))
    | spl11_8 ),
    inference(avatar_component_clause,[],[f452])).

fof(f454,plain,
    ( ~ spl11_8
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f450,f87,f452])).

fof(f87,plain,
    ( spl11_6
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK10(X0,X1,X2),sK1)
        | ~ r2_hidden(sK9(X0,X1,X2),sK0)
        | sK3 != X2
        | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f450,plain,
    ( ~ r2_hidden(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl11_6 ),
    inference(equality_resolution,[],[f449])).

fof(f449,plain,
    ( ! [X0] :
        ( sK3 != X0
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,
    ( ! [X0] :
        ( sK3 != X0
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl11_6 ),
    inference(resolution,[],[f445,f60])).

fof(f60,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f445,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK9(X0,sK1,X1),sK0)
        | sK3 != X1
        | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK1)) )
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK9(X0,sK1,X1),sK0)
        | sK3 != X1
        | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK1))
        | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK1)) )
    | ~ spl11_6 ),
    inference(resolution,[],[f88,f59])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK10(X0,X1,X2),sK1)
        | ~ r2_hidden(sK9(X0,X1,X2),sK0)
        | sK3 != X2
        | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) )
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f441,plain,
    ( spl11_7
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f437,f84,f62,f439])).

fof(f84,plain,
    ( spl11_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f437,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(resolution,[],[f305,f63])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,X1))
        | v1_xboole_0(X0) )
    | ~ spl11_5 ),
    inference(superposition,[],[f295,f38])).

fof(f295,plain,
    ( ! [X12,X11] : v1_xboole_0(k3_xboole_0(X11,k2_zfmisc_1(sK0,X12)))
    | ~ spl11_5 ),
    inference(resolution,[],[f128,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f128,plain,
    ( ! [X4,X5,X3] : ~ r2_hidden(X3,k3_xboole_0(X4,k2_zfmisc_1(sK0,X5)))
    | ~ spl11_5 ),
    inference(resolution,[],[f96,f54])).

fof(f96,plain,
    ( ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(sK0,X5))
    | ~ spl11_5 ),
    inference(resolution,[],[f92,f60])).

fof(f92,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl11_5 ),
    inference(resolution,[],[f85,f32])).

fof(f85,plain,
    ( v1_xboole_0(sK0)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f89,plain,
    ( spl11_5
    | spl11_6
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f82,f79,f87,f84])).

fof(f79,plain,
    ( spl11_4
  <=> ! [X1,X0,X2] :
        ( sK3 != X0
        | ~ r2_hidden(sK10(X1,X2,X0),sK1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ~ m1_subset_1(sK9(X1,X2,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK10(X0,X1,X2),sK1)
        | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
        | sK3 != X2
        | ~ r2_hidden(sK9(X0,X1,X2),sK0)
        | v1_xboole_0(sK0) )
    | ~ spl11_4 ),
    inference(resolution,[],[f80,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK9(X1,X2,X0),sK0)
        | ~ r2_hidden(sK10(X1,X2,X0),sK1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | sK3 != X0 )
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,
    ( spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f74,f79,f76])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sK3 != X0
      | ~ m1_subset_1(sK9(X1,X2,X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK10(X1,X2,X0),sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f73,f35])).

fof(f73,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(sK10(X5,X6,X7),sK1)
      | sK3 != X7
      | ~ m1_subset_1(sK9(X5,X6,X7),sK0)
      | ~ r2_hidden(X7,k2_zfmisc_1(X5,X6)) ) ),
    inference(superposition,[],[f31,f58])).

fof(f58,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f31,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ! [X4] :
        ( ! [X5] :
            ( k4_tarski(X4,X5) != sK3
            | ~ m1_subset_1(X5,sK1) )
        | ~ m1_subset_1(X4,sK0) )
    & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    & r2_hidden(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( ! [X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) )
   => ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != sK3
              | ~ m1_subset_1(X5,sK1) )
          | ~ m1_subset_1(X4,sK0) )
      & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(f68,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n023.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:19:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.40  % (25286)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.41  % (25278)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.42  % (25272)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.44  % (25288)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.18/0.45  % (25278)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.45  % SZS output start Proof for theBenchmark
% 0.18/0.45  fof(f1071,plain,(
% 0.18/0.45    $false),
% 0.18/0.45    inference(avatar_sat_refutation,[],[f64,f68,f81,f89,f441,f454,f470,f478,f1070])).
% 0.18/0.45  fof(f1070,plain,(
% 0.18/0.45    ~spl11_1 | ~spl11_2 | ~spl11_3),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f1069])).
% 0.18/0.45  fof(f1069,plain,(
% 0.18/0.45    $false | (~spl11_1 | ~spl11_2 | ~spl11_3)),
% 0.18/0.45    inference(subsumption_resolution,[],[f67,f1068])).
% 0.18/0.45  fof(f1068,plain,(
% 0.18/0.45    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl11_1 | ~spl11_3)),
% 0.18/0.45    inference(resolution,[],[f963,f63])).
% 0.18/0.45  fof(f63,plain,(
% 0.18/0.45    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl11_1),
% 0.18/0.45    inference(avatar_component_clause,[],[f62])).
% 0.18/0.45  fof(f62,plain,(
% 0.18/0.45    spl11_1 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.18/0.45  fof(f963,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,sK1)) | ~r2_hidden(X2,X0)) ) | ~spl11_3),
% 0.18/0.45    inference(superposition,[],[f538,f38])).
% 0.18/0.45  fof(f38,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f10])).
% 0.18/0.45  fof(f10,plain,(
% 0.18/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.18/0.45    inference(ennf_transformation,[],[f3])).
% 0.18/0.45  fof(f3,axiom,(
% 0.18/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.18/0.45  fof(f538,plain,(
% 0.18/0.45    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,k2_zfmisc_1(X5,sK1)))) ) | ~spl11_3),
% 0.18/0.45    inference(resolution,[],[f490,f54])).
% 0.18/0.45  fof(f54,plain,(
% 0.18/0.45    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.18/0.45    inference(equality_resolution,[],[f40])).
% 0.18/0.45  fof(f40,plain,(
% 0.18/0.45    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.18/0.45    inference(cnf_transformation,[],[f22])).
% 0.18/0.45  fof(f22,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).
% 0.18/0.45  fof(f21,plain,(
% 0.18/0.45    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f20,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.18/0.45    inference(rectify,[],[f19])).
% 0.18/0.45  fof(f19,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.18/0.45    inference(flattening,[],[f18])).
% 0.18/0.45  fof(f18,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.18/0.45    inference(nnf_transformation,[],[f2])).
% 0.18/0.45  fof(f2,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.18/0.45  fof(f490,plain,(
% 0.18/0.45    ( ! [X14,X15] : (~r2_hidden(X14,k2_zfmisc_1(X15,sK1))) ) | ~spl11_3),
% 0.18/0.45    inference(resolution,[],[f481,f59])).
% 0.18/0.45  fof(f59,plain,(
% 0.18/0.45    ( ! [X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.18/0.45    inference(equality_resolution,[],[f46])).
% 0.18/0.45  fof(f46,plain,(
% 0.18/0.45    ( ! [X2,X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.18/0.45    inference(cnf_transformation,[],[f28])).
% 0.18/0.45  fof(f28,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK6(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 & r2_hidden(sK10(X0,X1,X8),X1) & r2_hidden(sK9(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f24,f27,f26,f25])).
% 0.18/0.45  fof(f25,plain,(
% 0.18/0.45    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK6(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK6(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f26,plain,(
% 0.18/0.45    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK6(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f27,plain,(
% 0.18/0.45    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 & r2_hidden(sK10(X0,X1,X8),X1) & r2_hidden(sK9(X0,X1,X8),X0)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f24,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.45    inference(rectify,[],[f23])).
% 0.18/0.45  fof(f23,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.45    inference(nnf_transformation,[],[f4])).
% 0.18/0.45  fof(f4,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.18/0.45  fof(f481,plain,(
% 0.18/0.45    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl11_3),
% 0.18/0.45    inference(resolution,[],[f77,f32])).
% 0.18/0.45  fof(f32,plain,(
% 0.18/0.45    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f16])).
% 0.18/0.45  fof(f16,plain,(
% 0.18/0.45    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).
% 0.18/0.45  fof(f15,plain,(
% 0.18/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f14,plain,(
% 0.18/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.45    inference(rectify,[],[f13])).
% 0.18/0.45  fof(f13,plain,(
% 0.18/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.45    inference(nnf_transformation,[],[f1])).
% 0.18/0.45  fof(f1,axiom,(
% 0.18/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.45  fof(f77,plain,(
% 0.18/0.45    v1_xboole_0(sK1) | ~spl11_3),
% 0.18/0.45    inference(avatar_component_clause,[],[f76])).
% 0.18/0.45  fof(f76,plain,(
% 0.18/0.45    spl11_3 <=> v1_xboole_0(sK1)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.18/0.45  fof(f67,plain,(
% 0.18/0.45    r2_hidden(sK3,sK2) | ~spl11_2),
% 0.18/0.45    inference(avatar_component_clause,[],[f66])).
% 0.18/0.45  fof(f66,plain,(
% 0.18/0.45    spl11_2 <=> r2_hidden(sK3,sK2)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.18/0.45  fof(f478,plain,(
% 0.18/0.45    ~spl11_2 | ~spl11_7),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f477])).
% 0.18/0.45  fof(f477,plain,(
% 0.18/0.45    $false | (~spl11_2 | ~spl11_7)),
% 0.18/0.45    inference(subsumption_resolution,[],[f67,f476])).
% 0.18/0.45  fof(f476,plain,(
% 0.18/0.45    ( ! [X2] : (~r2_hidden(X2,sK2)) ) | ~spl11_7),
% 0.18/0.45    inference(resolution,[],[f440,f32])).
% 0.18/0.45  fof(f440,plain,(
% 0.18/0.45    v1_xboole_0(sK2) | ~spl11_7),
% 0.18/0.45    inference(avatar_component_clause,[],[f439])).
% 0.18/0.45  fof(f439,plain,(
% 0.18/0.45    spl11_7 <=> v1_xboole_0(sK2)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.18/0.45  fof(f470,plain,(
% 0.18/0.45    ~spl11_2 | ~spl11_1 | spl11_8),
% 0.18/0.45    inference(avatar_split_clause,[],[f468,f452,f62,f66])).
% 0.18/0.45  fof(f452,plain,(
% 0.18/0.45    spl11_8 <=> r2_hidden(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.18/0.45  fof(f468,plain,(
% 0.18/0.45    ~r2_hidden(sK3,sK2) | (~spl11_1 | spl11_8)),
% 0.18/0.45    inference(resolution,[],[f467,f63])).
% 0.18/0.45  fof(f467,plain,(
% 0.18/0.45    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK3,X0)) ) | spl11_8),
% 0.18/0.45    inference(superposition,[],[f459,f38])).
% 0.18/0.45  fof(f459,plain,(
% 0.18/0.45    ( ! [X1] : (~r2_hidden(sK3,k3_xboole_0(X1,k2_zfmisc_1(sK0,sK1)))) ) | spl11_8),
% 0.18/0.45    inference(resolution,[],[f453,f54])).
% 0.18/0.45  fof(f453,plain,(
% 0.18/0.45    ~r2_hidden(sK3,k2_zfmisc_1(sK0,sK1)) | spl11_8),
% 0.18/0.45    inference(avatar_component_clause,[],[f452])).
% 0.18/0.45  fof(f454,plain,(
% 0.18/0.45    ~spl11_8 | ~spl11_6),
% 0.18/0.45    inference(avatar_split_clause,[],[f450,f87,f452])).
% 0.18/0.45  fof(f87,plain,(
% 0.18/0.45    spl11_6 <=> ! [X1,X0,X2] : (~r2_hidden(sK10(X0,X1,X2),sK1) | ~r2_hidden(sK9(X0,X1,X2),sK0) | sK3 != X2 | ~r2_hidden(X2,k2_zfmisc_1(X0,X1)))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.18/0.45  fof(f450,plain,(
% 0.18/0.45    ~r2_hidden(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl11_6),
% 0.18/0.45    inference(equality_resolution,[],[f449])).
% 0.18/0.45  fof(f449,plain,(
% 0.18/0.45    ( ! [X0] : (sK3 != X0 | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl11_6),
% 0.18/0.45    inference(duplicate_literal_removal,[],[f446])).
% 0.18/0.45  fof(f446,plain,(
% 0.18/0.45    ( ! [X0] : (sK3 != X0 | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl11_6),
% 0.18/0.45    inference(resolution,[],[f445,f60])).
% 0.18/0.45  fof(f60,plain,(
% 0.18/0.45    ( ! [X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.18/0.45    inference(equality_resolution,[],[f45])).
% 0.18/0.45  fof(f45,plain,(
% 0.18/0.45    ( ! [X2,X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.18/0.45    inference(cnf_transformation,[],[f28])).
% 0.18/0.45  fof(f445,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~r2_hidden(sK9(X0,sK1,X1),sK0) | sK3 != X1 | ~r2_hidden(X1,k2_zfmisc_1(X0,sK1))) ) | ~spl11_6),
% 0.18/0.45    inference(duplicate_literal_removal,[],[f442])).
% 0.18/0.45  fof(f442,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~r2_hidden(sK9(X0,sK1,X1),sK0) | sK3 != X1 | ~r2_hidden(X1,k2_zfmisc_1(X0,sK1)) | ~r2_hidden(X1,k2_zfmisc_1(X0,sK1))) ) | ~spl11_6),
% 0.18/0.45    inference(resolution,[],[f88,f59])).
% 0.18/0.45  fof(f88,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r2_hidden(sK10(X0,X1,X2),sK1) | ~r2_hidden(sK9(X0,X1,X2),sK0) | sK3 != X2 | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) ) | ~spl11_6),
% 0.18/0.45    inference(avatar_component_clause,[],[f87])).
% 0.18/0.45  fof(f441,plain,(
% 0.18/0.45    spl11_7 | ~spl11_1 | ~spl11_5),
% 0.18/0.45    inference(avatar_split_clause,[],[f437,f84,f62,f439])).
% 0.18/0.45  fof(f84,plain,(
% 0.18/0.45    spl11_5 <=> v1_xboole_0(sK0)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.18/0.45  fof(f437,plain,(
% 0.18/0.45    v1_xboole_0(sK2) | (~spl11_1 | ~spl11_5)),
% 0.18/0.45    inference(resolution,[],[f305,f63])).
% 0.18/0.45  fof(f305,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(sK0,X1)) | v1_xboole_0(X0)) ) | ~spl11_5),
% 0.18/0.45    inference(superposition,[],[f295,f38])).
% 0.18/0.45  fof(f295,plain,(
% 0.18/0.45    ( ! [X12,X11] : (v1_xboole_0(k3_xboole_0(X11,k2_zfmisc_1(sK0,X12)))) ) | ~spl11_5),
% 0.18/0.45    inference(resolution,[],[f128,f33])).
% 0.18/0.45  fof(f33,plain,(
% 0.18/0.45    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f16])).
% 0.18/0.45  fof(f128,plain,(
% 0.18/0.45    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,k2_zfmisc_1(sK0,X5)))) ) | ~spl11_5),
% 0.18/0.45    inference(resolution,[],[f96,f54])).
% 0.18/0.45  fof(f96,plain,(
% 0.18/0.45    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(sK0,X5))) ) | ~spl11_5),
% 0.18/0.45    inference(resolution,[],[f92,f60])).
% 0.18/0.45  fof(f92,plain,(
% 0.18/0.45    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl11_5),
% 0.18/0.45    inference(resolution,[],[f85,f32])).
% 0.18/0.45  fof(f85,plain,(
% 0.18/0.45    v1_xboole_0(sK0) | ~spl11_5),
% 0.18/0.45    inference(avatar_component_clause,[],[f84])).
% 0.18/0.45  fof(f89,plain,(
% 0.18/0.45    spl11_5 | spl11_6 | ~spl11_4),
% 0.18/0.45    inference(avatar_split_clause,[],[f82,f79,f87,f84])).
% 0.18/0.45  fof(f79,plain,(
% 0.18/0.45    spl11_4 <=> ! [X1,X0,X2] : (sK3 != X0 | ~r2_hidden(sK10(X1,X2,X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(sK9(X1,X2,X0),sK0))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.18/0.45  fof(f82,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r2_hidden(sK10(X0,X1,X2),sK1) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | sK3 != X2 | ~r2_hidden(sK9(X0,X1,X2),sK0) | v1_xboole_0(sK0)) ) | ~spl11_4),
% 0.18/0.45    inference(resolution,[],[f80,f35])).
% 0.18/0.45  fof(f35,plain,(
% 0.18/0.45    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f17])).
% 0.18/0.45  fof(f17,plain,(
% 0.18/0.45    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.18/0.45    inference(nnf_transformation,[],[f9])).
% 0.18/0.45  fof(f9,plain,(
% 0.18/0.45    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.18/0.45    inference(ennf_transformation,[],[f5])).
% 0.18/0.45  fof(f5,axiom,(
% 0.18/0.45    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.18/0.45  fof(f80,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(sK9(X1,X2,X0),sK0) | ~r2_hidden(sK10(X1,X2,X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sK3 != X0) ) | ~spl11_4),
% 0.18/0.45    inference(avatar_component_clause,[],[f79])).
% 0.18/0.45  fof(f81,plain,(
% 0.18/0.45    spl11_3 | spl11_4),
% 0.18/0.45    inference(avatar_split_clause,[],[f74,f79,f76])).
% 0.18/0.45  fof(f74,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (sK3 != X0 | ~m1_subset_1(sK9(X1,X2,X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK10(X1,X2,X0),sK1) | v1_xboole_0(sK1)) )),
% 0.18/0.45    inference(resolution,[],[f73,f35])).
% 0.18/0.45  fof(f73,plain,(
% 0.18/0.45    ( ! [X6,X7,X5] : (~m1_subset_1(sK10(X5,X6,X7),sK1) | sK3 != X7 | ~m1_subset_1(sK9(X5,X6,X7),sK0) | ~r2_hidden(X7,k2_zfmisc_1(X5,X6))) )),
% 0.18/0.45    inference(superposition,[],[f31,f58])).
% 0.18/0.45  fof(f58,plain,(
% 0.18/0.45    ( ! [X0,X8,X1] : (k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.18/0.45    inference(equality_resolution,[],[f47])).
% 0.18/0.45  fof(f47,plain,(
% 0.18/0.45    ( ! [X2,X0,X8,X1] : (k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.18/0.45    inference(cnf_transformation,[],[f28])).
% 0.18/0.45  fof(f31,plain,(
% 0.18/0.45    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1) | ~m1_subset_1(X4,sK0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f12])).
% 0.18/0.45  fof(f12,plain,(
% 0.18/0.45    ! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2)),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f11])).
% 0.18/0.45  fof(f11,plain,(
% 0.18/0.45    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2)) => (! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f8,plain,(
% 0.18/0.45    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.18/0.45    inference(ennf_transformation,[],[f7])).
% 0.18/0.45  fof(f7,negated_conjecture,(
% 0.18/0.45    ~! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.18/0.45    inference(negated_conjecture,[],[f6])).
% 0.18/0.45  fof(f6,conjecture,(
% 0.18/0.45    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).
% 0.18/0.45  fof(f68,plain,(
% 0.18/0.45    spl11_2),
% 0.18/0.45    inference(avatar_split_clause,[],[f29,f66])).
% 0.18/0.45  fof(f29,plain,(
% 0.18/0.45    r2_hidden(sK3,sK2)),
% 0.18/0.45    inference(cnf_transformation,[],[f12])).
% 0.18/0.45  fof(f64,plain,(
% 0.18/0.45    spl11_1),
% 0.18/0.45    inference(avatar_split_clause,[],[f30,f62])).
% 0.18/0.45  fof(f30,plain,(
% 0.18/0.45    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.18/0.45    inference(cnf_transformation,[],[f12])).
% 0.18/0.45  % SZS output end Proof for theBenchmark
% 0.18/0.45  % (25278)------------------------------
% 0.18/0.45  % (25278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (25278)Termination reason: Refutation
% 0.18/0.45  
% 0.18/0.45  % (25278)Memory used [KB]: 11385
% 0.18/0.45  % (25278)Time elapsed: 0.065 s
% 0.18/0.45  % (25278)------------------------------
% 0.18/0.45  % (25278)------------------------------
% 0.18/0.45  % (25276)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.46  % (25271)Success in time 0.112 s
%------------------------------------------------------------------------------
