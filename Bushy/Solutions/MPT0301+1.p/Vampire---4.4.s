%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t113_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:58 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 195 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  304 ( 850 expanded)
%              Number of equality atoms :  112 ( 336 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f68,f78,f122,f130,f138,f227,f241,f255,f264])).

fof(f264,plain,
    ( spl8_7
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f256,f67])).

fof(f67,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl8_7
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f256,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_14 ),
    inference(resolution,[],[f237,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',t7_xboole_0)).

fof(f237,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl8_14
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f255,plain,
    ( spl8_3
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f247,f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f247,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_16 ),
    inference(resolution,[],[f240,f36])).

fof(f240,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl8_16
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f241,plain,
    ( spl8_14
    | spl8_16
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f234,f127,f70,f239,f236])).

fof(f70,plain,
    ( spl8_8
  <=> k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f127,plain,
    ( spl8_12
  <=> ! [X10] : ~ r2_hidden(X10,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f228,f128])).

fof(f128,plain,
    ( ! [X10] : ~ r2_hidden(X10,k1_xboole_0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_8 ),
    inference(superposition,[],[f49,f71])).

fof(f71,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f49,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = sK3(X0,X1,X2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f26,f29,f28,f27])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',d2_zfmisc_1)).

fof(f227,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl8_5 ),
    inference(resolution,[],[f225,f34])).

fof(f34,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(f225,plain,
    ( ! [X25] : ~ v1_xboole_0(X25)
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f223,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',t6_boole)).

fof(f223,plain,
    ( ! [X25] :
        ( k1_xboole_0 != X25
        | ~ v1_xboole_0(X25) )
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( ! [X25] :
        ( k1_xboole_0 != X25
        | ~ v1_xboole_0(X25)
        | ~ v1_xboole_0(X25) )
    | ~ spl8_5 ),
    inference(superposition,[],[f132,f95])).

fof(f95,plain,(
    ! [X4,X5] :
      ( k2_zfmisc_1(X4,X5) = k1_xboole_0
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f86,f36])).

fof(f86,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',t7_boole)).

fof(f52,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f132,plain,
    ( ! [X0] :
        ( k2_zfmisc_1(X0,sK1) != X0
        | ~ v1_xboole_0(X0) )
    | ~ spl8_5 ),
    inference(superposition,[],[f64,f35])).

fof(f64,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_5
  <=> k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f138,plain,(
    ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl8_10 ),
    inference(resolution,[],[f125,f34])).

fof(f125,plain,
    ( ! [X9] : ~ v1_xboole_0(X9)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_10
  <=> ! [X9] : ~ v1_xboole_0(X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f130,plain,
    ( spl8_10
    | spl8_10
    | spl8_12 ),
    inference(avatar_split_clause,[],[f108,f127,f124,f124])).

fof(f108,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(superposition,[],[f86,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X1,X0) = k1_xboole_0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f84,f36])).

fof(f84,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f51,f39])).

fof(f51,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f122,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl8_1 ),
    inference(resolution,[],[f114,f34])).

fof(f114,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | ~ v1_xboole_0(X0) )
    | ~ spl8_1 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f80,f87])).

fof(f80,plain,
    ( ! [X0] :
        ( k2_zfmisc_1(sK0,X0) != X0
        | ~ v1_xboole_0(X0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f56,f35])).

fof(f56,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl8_1
  <=> k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f78,plain,
    ( spl8_8
    | spl8_6
    | spl8_2 ),
    inference(avatar_split_clause,[],[f31,f76,f73,f70])).

fof(f73,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f76,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f31,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k2_zfmisc_1(sK0,sK1) != k1_xboole_0 )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k2_zfmisc_1(X0,X1) != k1_xboole_0 )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) )
   => ( ( ( k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 )
        | k2_zfmisc_1(sK0,sK1) != k1_xboole_0 )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',t113_zfmisc_1)).

fof(f68,plain,
    ( ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f61,f66,f63])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(inner_rewriting,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK0
    | k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f53,f58,f55])).

fof(f53,plain,
    ( k1_xboole_0 != sK1
    | k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(inner_rewriting,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
