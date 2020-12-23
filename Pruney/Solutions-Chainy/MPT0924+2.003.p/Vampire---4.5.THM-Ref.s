%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:50 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 522 expanded)
%              Number of leaves         :   34 ( 186 expanded)
%              Depth                    :   15
%              Number of atoms          :  599 (3085 expanded)
%              Number of equality atoms :   52 ( 449 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1024,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f98,f99,f100,f101,f115,f212,f216,f226,f850,f863,f903,f915,f934,f958,f965,f977,f987,f993,f999,f1011,f1013,f1015,f1022])).

fof(f1022,plain,(
    ~ spl15_20 ),
    inference(avatar_contradiction_clause,[],[f1018])).

fof(f1018,plain,
    ( $false
    | ~ spl15_20 ),
    inference(resolution,[],[f973,f38])).

fof(f38,plain,(
    ! [X0] : r2_hidden(X0,sK8(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(X2,sK8(X0))
          | r2_tarski(X2,sK8(X0))
          | ~ r1_tarski(X2,sK8(X0)) )
      & ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),sK8(X0))
          | ~ r2_hidden(X3,sK8(X0)) )
      & ! [X4,X5] :
          ( r2_hidden(X5,sK8(X0))
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,sK8(X0)) )
      & r2_hidden(X0,sK8(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f14,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | r2_tarski(X2,X1)
              | ~ r1_tarski(X2,X1) )
          & ! [X3] :
              ( r2_hidden(k1_zfmisc_1(X3),X1)
              | ~ r2_hidden(X3,X1) )
          & ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r1_tarski(X5,X4)
              | ~ r2_hidden(X4,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(X2,sK8(X0))
            | r2_tarski(X2,sK8(X0))
            | ~ r1_tarski(X2,sK8(X0)) )
        & ! [X3] :
            ( r2_hidden(k1_zfmisc_1(X3),sK8(X0))
            | ~ r2_hidden(X3,sK8(X0)) )
        & ! [X5,X4] :
            ( r2_hidden(X5,sK8(X0))
            | ~ r1_tarski(X5,X4)
            | ~ r2_hidden(X4,sK8(X0)) )
        & r2_hidden(X0,sK8(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(k1_zfmisc_1(X3),X1) )
      & ! [X4,X5] :
          ( ( r1_tarski(X5,X4)
            & r2_hidden(X4,X1) )
         => r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k1_zfmisc_1(X2),X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(f973,plain,
    ( ! [X1] : ~ r2_hidden(sK0,X1)
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f972])).

fof(f972,plain,
    ( spl15_20
  <=> ! [X1] : ~ r2_hidden(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f1015,plain,
    ( spl15_23
    | spl15_3
    | ~ spl15_21 ),
    inference(avatar_split_clause,[],[f978,f975,f86,f985])).

fof(f985,plain,
    ( spl15_23
  <=> ! [X0] : ~ r2_hidden(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).

fof(f86,plain,
    ( spl15_3
  <=> r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f975,plain,
    ( spl15_21
  <=> ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_21])])).

fof(f978,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,sK5)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl15_21 ),
    inference(resolution,[],[f976,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(sK9(X0,X1,X2),X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f976,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK5))
    | ~ spl15_21 ),
    inference(avatar_component_clause,[],[f975])).

fof(f1013,plain,
    ( spl15_16
    | spl15_4
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f916,f913,f90,f923])).

fof(f923,plain,
    ( spl15_16
  <=> ! [X2] : ~ r2_hidden(sK2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f90,plain,
    ( spl15_4
  <=> r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f913,plain,
    ( spl15_15
  <=> ! [X0] : ~ r2_hidden(sK2,k4_xboole_0(X0,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f916,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,sK6)
        | ~ r2_hidden(sK2,X0) )
    | ~ spl15_15 ),
    inference(resolution,[],[f914,f69])).

fof(f914,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k4_xboole_0(X0,sK6))
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f913])).

fof(f1011,plain,
    ( spl15_20
    | spl15_2
    | ~ spl15_22 ),
    inference(avatar_split_clause,[],[f1003,f982,f82,f972])).

fof(f82,plain,
    ( spl15_2
  <=> r2_hidden(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f982,plain,
    ( spl15_22
  <=> ! [X1] : ~ r2_hidden(sK0,k4_xboole_0(X1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f1003,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,sK4)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl15_22 ),
    inference(resolution,[],[f983,f69])).

fof(f983,plain,
    ( ! [X1] : ~ r2_hidden(sK0,k4_xboole_0(X1,sK4))
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f982])).

fof(f999,plain,(
    ~ spl15_23 ),
    inference(avatar_contradiction_clause,[],[f995])).

fof(f995,plain,
    ( $false
    | ~ spl15_23 ),
    inference(resolution,[],[f986,f38])).

fof(f986,plain,
    ( ! [X0] : ~ r2_hidden(sK1,X0)
    | ~ spl15_23 ),
    inference(avatar_component_clause,[],[f985])).

fof(f993,plain,(
    ~ spl15_14 ),
    inference(avatar_contradiction_clause,[],[f989])).

fof(f989,plain,
    ( $false
    | ~ spl15_14 ),
    inference(resolution,[],[f911,f38])).

fof(f911,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(sK0,sK1),X1)
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f910])).

fof(f910,plain,
    ( spl15_14
  <=> ! [X1] : ~ r2_hidden(k4_tarski(sK0,sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f987,plain,
    ( spl15_22
    | spl15_23
    | ~ spl15_19 ),
    inference(avatar_split_clause,[],[f980,f962,f985,f982])).

fof(f962,plain,
    ( spl15_19
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f980,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r2_hidden(sK0,k4_xboole_0(X1,sK4)) )
    | ~ spl15_19 ),
    inference(resolution,[],[f969,f153])).

fof(f153,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(k1_mcart_1(k4_tarski(X5,X8)),X7)
      | ~ r2_hidden(X8,X9)
      | ~ r2_hidden(X5,k4_xboole_0(X6,X7)) ) ),
    inference(resolution,[],[f108,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,(
    ! [X14,X12,X15,X13] :
      ( r2_hidden(k1_mcart_1(k4_tarski(X14,X12)),X15)
      | ~ r2_hidden(X14,X15)
      | ~ r2_hidden(X12,X13) ) ),
    inference(resolution,[],[f73,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f73,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK10(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( ( sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2))
              & r2_hidden(sK12(X0,X1,X2),X1)
              & r2_hidden(sK11(X0,X1,X2),X0) )
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8
                & r2_hidden(sK14(X0,X1,X8),X1)
                & r2_hidden(sK13(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13,sK14])],[f28,f31,f30,f29])).

fof(f29,plain,(
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
              ( k4_tarski(X4,X5) != sK10(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK10(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK10(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2))
        & r2_hidden(sK12(X0,X1,X2),X1)
        & r2_hidden(sK11(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8
        & r2_hidden(sK14(X0,X1,X8),X1)
        & r2_hidden(sK13(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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

fof(f969,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(sK0,sK1)),sK4)
    | ~ spl15_19 ),
    inference(resolution,[],[f964,f44])).

fof(f964,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl15_19 ),
    inference(avatar_component_clause,[],[f962])).

fof(f977,plain,
    ( spl15_20
    | spl15_21
    | ~ spl15_19 ),
    inference(avatar_split_clause,[],[f970,f962,f975,f972])).

fof(f970,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,k4_xboole_0(X0,sK5))
        | ~ r2_hidden(sK0,X1) )
    | ~ spl15_19 ),
    inference(resolution,[],[f968,f146])).

fof(f146,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(k2_mcart_1(k4_tarski(X5,X7)),X9)
      | ~ r2_hidden(X7,k4_xboole_0(X8,X9))
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f107,f70])).

fof(f107,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(k2_mcart_1(k4_tarski(X10,X8)),X9)
      | ~ r2_hidden(X10,X11)
      | ~ r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f968,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK0,sK1)),sK5)
    | ~ spl15_19 ),
    inference(resolution,[],[f964,f45])).

fof(f965,plain,
    ( spl15_14
    | spl15_19
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f959,f956,f962,f910])).

fof(f956,plain,
    ( spl15_18
  <=> ! [X1] : ~ r2_hidden(k4_tarski(sK0,sK1),k4_xboole_0(X1,k2_zfmisc_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f959,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
        | ~ r2_hidden(k4_tarski(sK0,sK1),X0) )
    | ~ spl15_18 ),
    inference(resolution,[],[f957,f69])).

fof(f957,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(sK0,sK1),k4_xboole_0(X1,k2_zfmisc_1(sK4,sK5)))
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f956])).

fof(f958,plain,
    ( spl15_18
    | spl15_16
    | ~ spl15_13 ),
    inference(avatar_split_clause,[],[f950,f900,f923,f956])).

fof(f900,plain,
    ( spl15_13
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f950,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2,X0)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k4_xboole_0(X1,k2_zfmisc_1(sK4,sK5))) )
    | ~ spl15_13 ),
    inference(resolution,[],[f907,f153])).

fof(f907,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_zfmisc_1(sK4,sK5))
    | ~ spl15_13 ),
    inference(resolution,[],[f902,f44])).

fof(f902,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl15_13 ),
    inference(avatar_component_clause,[],[f900])).

fof(f934,plain,(
    ~ spl15_16 ),
    inference(avatar_contradiction_clause,[],[f930])).

fof(f930,plain,
    ( $false
    | ~ spl15_16 ),
    inference(resolution,[],[f924,f38])).

fof(f924,plain,
    ( ! [X2] : ~ r2_hidden(sK2,X2)
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f923])).

fof(f915,plain,
    ( spl15_14
    | spl15_15
    | ~ spl15_13 ),
    inference(avatar_split_clause,[],[f908,f900,f913,f910])).

fof(f908,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2,k4_xboole_0(X0,sK6))
        | ~ r2_hidden(k4_tarski(sK0,sK1),X1) )
    | ~ spl15_13 ),
    inference(resolution,[],[f906,f146])).

fof(f906,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),sK6)
    | ~ spl15_13 ),
    inference(resolution,[],[f902,f45])).

fof(f903,plain,
    ( spl15_6
    | spl15_13
    | ~ spl15_12 ),
    inference(avatar_split_clause,[],[f897,f848,f900,f207])).

fof(f207,plain,
    ( spl15_6
  <=> ! [X14] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f848,plain,
    ( spl15_12
  <=> ! [X1] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_xboole_0(X1,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f897,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X0) )
    | ~ spl15_12 ),
    inference(resolution,[],[f849,f69])).

fof(f849,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_xboole_0(X1,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)))
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f848])).

fof(f863,plain,(
    ~ spl15_8 ),
    inference(avatar_contradiction_clause,[],[f859])).

fof(f859,plain,
    ( $false
    | ~ spl15_8 ),
    inference(resolution,[],[f225,f38])).

fof(f225,plain,
    ( ! [X0] : ~ r2_hidden(sK3,X0)
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl15_8
  <=> ! [X0] : ~ r2_hidden(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f850,plain,
    ( spl15_12
    | spl15_8
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f836,f78,f224,f848])).

fof(f78,plain,
    ( spl15_1
  <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f836,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_xboole_0(X1,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))) )
    | ~ spl15_1 ),
    inference(resolution,[],[f153,f119])).

fof(f119,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl15_1 ),
    inference(resolution,[],[f79,f44])).

fof(f79,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f226,plain,
    ( spl15_8
    | spl15_5
    | ~ spl15_7 ),
    inference(avatar_split_clause,[],[f217,f210,f94,f224])).

fof(f94,plain,
    ( spl15_5
  <=> r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f210,plain,
    ( spl15_7
  <=> ! [X13] : ~ r2_hidden(sK3,k4_xboole_0(X13,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f217,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,sK7)
        | ~ r2_hidden(sK3,X0) )
    | ~ spl15_7 ),
    inference(resolution,[],[f211,f69])).

fof(f211,plain,
    ( ! [X13] : ~ r2_hidden(sK3,k4_xboole_0(X13,sK7))
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f210])).

fof(f216,plain,(
    ~ spl15_6 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl15_6 ),
    inference(resolution,[],[f208,f38])).

fof(f208,plain,
    ( ! [X14] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X14)
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f207])).

fof(f212,plain,
    ( spl15_6
    | spl15_7
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f198,f78,f210,f207])).

fof(f198,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(sK3,k4_xboole_0(X13,sK7))
        | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X14) )
    | ~ spl15_1 ),
    inference(resolution,[],[f146,f118])).

fof(f118,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),sK7)
    | ~ spl15_1 ),
    inference(resolution,[],[f79,f45])).

fof(f115,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_3
    | ~ spl15_4
    | ~ spl15_5 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl15_1
    | ~ spl15_2
    | ~ spl15_3
    | ~ spl15_4
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f113,f83])).

fof(f83,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f113,plain,
    ( ~ r2_hidden(sK0,sK4)
    | spl15_1
    | ~ spl15_3
    | ~ spl15_4
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f112,f87])).

fof(f87,plain,
    ( r2_hidden(sK1,sK5)
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f112,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | spl15_1
    | ~ spl15_4
    | ~ spl15_5 ),
    inference(resolution,[],[f111,f73])).

fof(f111,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl15_1
    | ~ spl15_4
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f110,f91])).

fof(f91,plain,
    ( r2_hidden(sK2,sK6)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f110,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl15_1
    | ~ spl15_5 ),
    inference(resolution,[],[f109,f73])).

fof(f109,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl15_1
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f104,f95])).

fof(f95,plain,
    ( r2_hidden(sK3,sK7)
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f104,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl15_1 ),
    inference(resolution,[],[f73,f80])).

fof(f80,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | spl15_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f101,plain,
    ( spl15_1
    | spl15_2 ),
    inference(avatar_split_clause,[],[f68,f82,f78])).

fof(f68,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f33,f63,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f61,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f60,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f33,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r2_hidden(sK3,sK7)
      | ~ r2_hidden(sK2,sK6)
      | ~ r2_hidden(sK1,sK5)
      | ~ r2_hidden(sK0,sK4)
      | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
    & ( ( r2_hidden(sK3,sK7)
        & r2_hidden(sK2,sK6)
        & r2_hidden(sK1,sK5)
        & r2_hidden(sK0,sK4) )
      | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( ~ r2_hidden(X3,X7)
          | ~ r2_hidden(X2,X6)
          | ~ r2_hidden(X1,X5)
          | ~ r2_hidden(X0,X4)
          | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
        & ( ( r2_hidden(X3,X7)
            & r2_hidden(X2,X6)
            & r2_hidden(X1,X5)
            & r2_hidden(X0,X4) )
          | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) )
   => ( ( ~ r2_hidden(sK3,sK7)
        | ~ r2_hidden(sK2,sK6)
        | ~ r2_hidden(sK1,sK5)
        | ~ r2_hidden(sK0,sK4)
        | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
      & ( ( r2_hidden(sK3,sK7)
          & r2_hidden(sK2,sK6)
          & r2_hidden(sK1,sK5)
          & r2_hidden(sK0,sK4) )
        | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

fof(f100,plain,
    ( spl15_1
    | spl15_3 ),
    inference(avatar_split_clause,[],[f67,f86,f78])).

fof(f67,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f34,f63,f62])).

fof(f34,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,
    ( spl15_1
    | spl15_4 ),
    inference(avatar_split_clause,[],[f66,f90,f78])).

fof(f66,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f35,f63,f62])).

fof(f35,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,
    ( spl15_1
    | spl15_5 ),
    inference(avatar_split_clause,[],[f65,f94,f78])).

fof(f65,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f36,f63,f62])).

fof(f36,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,
    ( ~ spl15_1
    | ~ spl15_2
    | ~ spl15_3
    | ~ spl15_4
    | ~ spl15_5 ),
    inference(avatar_split_clause,[],[f64,f94,f90,f86,f82,f78])).

fof(f64,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f37,f63,f62])).

fof(f37,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (28045)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (28039)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (28038)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (28052)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (28059)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (28057)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (28067)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (28041)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (28053)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (28043)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (28051)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (28047)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (28042)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28049)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (28044)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (28049)Refutation not found, incomplete strategy% (28049)------------------------------
% 0.21/0.54  % (28049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28049)Memory used [KB]: 10618
% 0.21/0.54  % (28049)Time elapsed: 0.129 s
% 0.21/0.54  % (28049)------------------------------
% 0.21/0.54  % (28049)------------------------------
% 0.21/0.54  % (28046)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (28050)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (28056)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (28040)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (28048)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (28048)Refutation not found, incomplete strategy% (28048)------------------------------
% 0.21/0.54  % (28048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28048)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28048)Memory used [KB]: 10618
% 0.21/0.54  % (28048)Time elapsed: 0.136 s
% 0.21/0.54  % (28048)------------------------------
% 0.21/0.54  % (28048)------------------------------
% 0.21/0.54  % (28063)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (28066)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (28061)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28064)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (28054)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (28055)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (28055)Refutation not found, incomplete strategy% (28055)------------------------------
% 0.21/0.55  % (28055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28060)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (28055)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28055)Memory used [KB]: 10618
% 0.21/0.55  % (28055)Time elapsed: 0.144 s
% 0.21/0.55  % (28055)------------------------------
% 0.21/0.55  % (28055)------------------------------
% 0.21/0.55  % (28058)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (28062)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (28060)Refutation not found, incomplete strategy% (28060)------------------------------
% 0.21/0.57  % (28060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (28060)Memory used [KB]: 10874
% 0.21/0.57  % (28060)Time elapsed: 0.152 s
% 0.21/0.57  % (28060)------------------------------
% 0.21/0.57  % (28060)------------------------------
% 0.21/0.58  % (28065)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.11/0.65  % (28041)Refutation found. Thanks to Tanya!
% 2.11/0.65  % SZS status Theorem for theBenchmark
% 2.11/0.65  % SZS output start Proof for theBenchmark
% 2.11/0.65  fof(f1024,plain,(
% 2.11/0.65    $false),
% 2.11/0.65    inference(avatar_sat_refutation,[],[f97,f98,f99,f100,f101,f115,f212,f216,f226,f850,f863,f903,f915,f934,f958,f965,f977,f987,f993,f999,f1011,f1013,f1015,f1022])).
% 2.11/0.65  fof(f1022,plain,(
% 2.11/0.65    ~spl15_20),
% 2.11/0.65    inference(avatar_contradiction_clause,[],[f1018])).
% 2.11/0.65  fof(f1018,plain,(
% 2.11/0.65    $false | ~spl15_20),
% 2.11/0.65    inference(resolution,[],[f973,f38])).
% 2.11/0.65  fof(f38,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(X0,sK8(X0))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f21])).
% 2.11/0.65  fof(f21,plain,(
% 2.11/0.65    ! [X0] : (! [X2] : (r2_hidden(X2,sK8(X0)) | r2_tarski(X2,sK8(X0)) | ~r1_tarski(X2,sK8(X0))) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),sK8(X0)) | ~r2_hidden(X3,sK8(X0))) & ! [X4,X5] : (r2_hidden(X5,sK8(X0)) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,sK8(X0))) & r2_hidden(X0,sK8(X0)))),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f14,f20])).
% 2.11/0.65  fof(f20,plain,(
% 2.11/0.65    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(X2,sK8(X0)) | r2_tarski(X2,sK8(X0)) | ~r1_tarski(X2,sK8(X0))) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),sK8(X0)) | ~r2_hidden(X3,sK8(X0))) & ! [X5,X4] : (r2_hidden(X5,sK8(X0)) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,sK8(X0))) & r2_hidden(X0,sK8(X0))))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f14,plain,(
% 2.11/0.65    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,X1)) & r2_hidden(X0,X1))),
% 2.11/0.65    inference(flattening,[],[f13])).
% 2.11/0.65  fof(f13,plain,(
% 2.11/0.65    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | (~r1_tarski(X5,X4) | ~r2_hidden(X4,X1))) & r2_hidden(X0,X1))),
% 2.11/0.65    inference(ennf_transformation,[],[f11])).
% 2.11/0.65  fof(f11,plain,(
% 2.11/0.65    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(X3,X1) => r2_hidden(k1_zfmisc_1(X3),X1)) & ! [X4,X5] : ((r1_tarski(X5,X4) & r2_hidden(X4,X1)) => r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 2.11/0.65    inference(rectify,[],[f3])).
% 2.11/0.65  fof(f3,axiom,(
% 2.11/0.65    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k1_zfmisc_1(X2),X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).
% 2.11/0.65  fof(f973,plain,(
% 2.11/0.65    ( ! [X1] : (~r2_hidden(sK0,X1)) ) | ~spl15_20),
% 2.11/0.65    inference(avatar_component_clause,[],[f972])).
% 2.11/0.65  fof(f972,plain,(
% 2.11/0.65    spl15_20 <=> ! [X1] : ~r2_hidden(sK0,X1)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).
% 2.11/0.65  fof(f1015,plain,(
% 2.11/0.65    spl15_23 | spl15_3 | ~spl15_21),
% 2.11/0.65    inference(avatar_split_clause,[],[f978,f975,f86,f985])).
% 2.11/0.65  fof(f985,plain,(
% 2.11/0.65    spl15_23 <=> ! [X0] : ~r2_hidden(sK1,X0)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).
% 2.11/0.65  fof(f86,plain,(
% 2.11/0.65    spl15_3 <=> r2_hidden(sK1,sK5)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).
% 2.11/0.65  fof(f975,plain,(
% 2.11/0.65    spl15_21 <=> ! [X0] : ~r2_hidden(sK1,k4_xboole_0(X0,sK5))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_21])])).
% 2.11/0.65  fof(f978,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(sK1,sK5) | ~r2_hidden(sK1,X0)) ) | ~spl15_21),
% 2.11/0.65    inference(resolution,[],[f976,f69])).
% 2.11/0.65  fof(f69,plain,(
% 2.11/0.65    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.11/0.65    inference(equality_resolution,[],[f48])).
% 2.11/0.65  fof(f48,plain,(
% 2.11/0.65    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.11/0.65    inference(cnf_transformation,[],[f26])).
% 2.11/0.65  fof(f26,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((~r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f25])).
% 2.11/0.65  fof(f25,plain,(
% 2.11/0.65    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((~r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f24,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.11/0.65    inference(rectify,[],[f23])).
% 2.11/0.65  fof(f23,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.11/0.65    inference(flattening,[],[f22])).
% 2.11/0.65  fof(f22,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.11/0.65    inference(nnf_transformation,[],[f1])).
% 2.11/0.65  fof(f1,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.11/0.65  fof(f976,plain,(
% 2.11/0.65    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,sK5))) ) | ~spl15_21),
% 2.11/0.65    inference(avatar_component_clause,[],[f975])).
% 2.11/0.65  fof(f1013,plain,(
% 2.11/0.65    spl15_16 | spl15_4 | ~spl15_15),
% 2.11/0.65    inference(avatar_split_clause,[],[f916,f913,f90,f923])).
% 2.11/0.65  fof(f923,plain,(
% 2.11/0.65    spl15_16 <=> ! [X2] : ~r2_hidden(sK2,X2)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).
% 2.11/0.65  fof(f90,plain,(
% 2.11/0.65    spl15_4 <=> r2_hidden(sK2,sK6)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).
% 2.11/0.65  fof(f913,plain,(
% 2.11/0.65    spl15_15 <=> ! [X0] : ~r2_hidden(sK2,k4_xboole_0(X0,sK6))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).
% 2.11/0.65  fof(f916,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(sK2,sK6) | ~r2_hidden(sK2,X0)) ) | ~spl15_15),
% 2.11/0.65    inference(resolution,[],[f914,f69])).
% 2.11/0.65  fof(f914,plain,(
% 2.11/0.65    ( ! [X0] : (~r2_hidden(sK2,k4_xboole_0(X0,sK6))) ) | ~spl15_15),
% 2.11/0.65    inference(avatar_component_clause,[],[f913])).
% 2.11/0.65  fof(f1011,plain,(
% 2.11/0.65    spl15_20 | spl15_2 | ~spl15_22),
% 2.11/0.65    inference(avatar_split_clause,[],[f1003,f982,f82,f972])).
% 2.11/0.65  fof(f82,plain,(
% 2.11/0.65    spl15_2 <=> r2_hidden(sK0,sK4)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 2.11/0.65  fof(f982,plain,(
% 2.11/0.65    spl15_22 <=> ! [X1] : ~r2_hidden(sK0,k4_xboole_0(X1,sK4))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).
% 2.11/0.65  fof(f1003,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(sK0,sK4) | ~r2_hidden(sK0,X0)) ) | ~spl15_22),
% 2.11/0.65    inference(resolution,[],[f983,f69])).
% 2.11/0.65  fof(f983,plain,(
% 2.11/0.65    ( ! [X1] : (~r2_hidden(sK0,k4_xboole_0(X1,sK4))) ) | ~spl15_22),
% 2.11/0.65    inference(avatar_component_clause,[],[f982])).
% 2.11/0.65  fof(f999,plain,(
% 2.11/0.65    ~spl15_23),
% 2.11/0.65    inference(avatar_contradiction_clause,[],[f995])).
% 2.11/0.65  fof(f995,plain,(
% 2.11/0.65    $false | ~spl15_23),
% 2.11/0.65    inference(resolution,[],[f986,f38])).
% 2.11/0.65  fof(f986,plain,(
% 2.11/0.65    ( ! [X0] : (~r2_hidden(sK1,X0)) ) | ~spl15_23),
% 2.11/0.65    inference(avatar_component_clause,[],[f985])).
% 2.11/0.65  fof(f993,plain,(
% 2.11/0.65    ~spl15_14),
% 2.11/0.65    inference(avatar_contradiction_clause,[],[f989])).
% 2.11/0.65  fof(f989,plain,(
% 2.11/0.65    $false | ~spl15_14),
% 2.11/0.65    inference(resolution,[],[f911,f38])).
% 2.11/0.65  fof(f911,plain,(
% 2.11/0.65    ( ! [X1] : (~r2_hidden(k4_tarski(sK0,sK1),X1)) ) | ~spl15_14),
% 2.11/0.65    inference(avatar_component_clause,[],[f910])).
% 2.11/0.65  fof(f910,plain,(
% 2.11/0.65    spl15_14 <=> ! [X1] : ~r2_hidden(k4_tarski(sK0,sK1),X1)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).
% 2.11/0.65  fof(f987,plain,(
% 2.11/0.65    spl15_22 | spl15_23 | ~spl15_19),
% 2.11/0.65    inference(avatar_split_clause,[],[f980,f962,f985,f982])).
% 2.11/0.65  fof(f962,plain,(
% 2.11/0.65    spl15_19 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).
% 2.11/0.65  fof(f980,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r2_hidden(sK1,X0) | ~r2_hidden(sK0,k4_xboole_0(X1,sK4))) ) | ~spl15_19),
% 2.11/0.65    inference(resolution,[],[f969,f153])).
% 2.11/0.65  fof(f153,plain,(
% 2.11/0.65    ( ! [X6,X8,X7,X5,X9] : (~r2_hidden(k1_mcart_1(k4_tarski(X5,X8)),X7) | ~r2_hidden(X8,X9) | ~r2_hidden(X5,k4_xboole_0(X6,X7))) )),
% 2.11/0.65    inference(resolution,[],[f108,f70])).
% 2.11/0.65  fof(f70,plain,(
% 2.11/0.65    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.11/0.65    inference(equality_resolution,[],[f47])).
% 2.11/0.65  fof(f47,plain,(
% 2.11/0.65    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.11/0.65    inference(cnf_transformation,[],[f26])).
% 2.11/0.65  fof(f108,plain,(
% 2.11/0.65    ( ! [X14,X12,X15,X13] : (r2_hidden(k1_mcart_1(k4_tarski(X14,X12)),X15) | ~r2_hidden(X14,X15) | ~r2_hidden(X12,X13)) )),
% 2.11/0.65    inference(resolution,[],[f73,f44])).
% 2.11/0.65  fof(f44,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f15])).
% 2.11/0.65  fof(f15,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.11/0.65    inference(ennf_transformation,[],[f8])).
% 2.11/0.65  fof(f8,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.11/0.65  fof(f73,plain,(
% 2.11/0.65    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 2.11/0.65    inference(equality_resolution,[],[f72])).
% 2.11/0.65  fof(f72,plain,(
% 2.11/0.65    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.11/0.65    inference(equality_resolution,[],[f55])).
% 2.11/0.65  fof(f55,plain,(
% 2.11/0.65    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.11/0.65    inference(cnf_transformation,[],[f32])).
% 2.11/0.65  fof(f32,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK10(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X0)) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8 & r2_hidden(sK14(X0,X1,X8),X1) & r2_hidden(sK13(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13,sK14])],[f28,f31,f30,f29])).
% 2.11/0.65  fof(f29,plain,(
% 2.11/0.65    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK10(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK10(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f30,plain,(
% 2.11/0.65    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK10(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X0)))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f31,plain,(
% 2.11/0.65    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8 & r2_hidden(sK14(X0,X1,X8),X1) & r2_hidden(sK13(X0,X1,X8),X0)))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f28,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.11/0.65    inference(rectify,[],[f27])).
% 2.11/0.65  fof(f27,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.11/0.65    inference(nnf_transformation,[],[f2])).
% 2.11/0.65  fof(f2,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.11/0.65  fof(f969,plain,(
% 2.11/0.65    r2_hidden(k1_mcart_1(k4_tarski(sK0,sK1)),sK4) | ~spl15_19),
% 2.11/0.65    inference(resolution,[],[f964,f44])).
% 2.11/0.65  fof(f964,plain,(
% 2.11/0.65    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | ~spl15_19),
% 2.11/0.65    inference(avatar_component_clause,[],[f962])).
% 2.11/0.65  fof(f977,plain,(
% 2.11/0.65    spl15_20 | spl15_21 | ~spl15_19),
% 2.11/0.65    inference(avatar_split_clause,[],[f970,f962,f975,f972])).
% 2.11/0.65  fof(f970,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r2_hidden(sK1,k4_xboole_0(X0,sK5)) | ~r2_hidden(sK0,X1)) ) | ~spl15_19),
% 2.11/0.65    inference(resolution,[],[f968,f146])).
% 2.11/0.65  fof(f146,plain,(
% 2.11/0.65    ( ! [X6,X8,X7,X5,X9] : (~r2_hidden(k2_mcart_1(k4_tarski(X5,X7)),X9) | ~r2_hidden(X7,k4_xboole_0(X8,X9)) | ~r2_hidden(X5,X6)) )),
% 2.11/0.65    inference(resolution,[],[f107,f70])).
% 2.11/0.65  fof(f107,plain,(
% 2.11/0.65    ( ! [X10,X8,X11,X9] : (r2_hidden(k2_mcart_1(k4_tarski(X10,X8)),X9) | ~r2_hidden(X10,X11) | ~r2_hidden(X8,X9)) )),
% 2.11/0.65    inference(resolution,[],[f73,f45])).
% 2.11/0.65  fof(f45,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f15])).
% 2.11/0.65  fof(f968,plain,(
% 2.11/0.65    r2_hidden(k2_mcart_1(k4_tarski(sK0,sK1)),sK5) | ~spl15_19),
% 2.11/0.65    inference(resolution,[],[f964,f45])).
% 2.11/0.65  fof(f965,plain,(
% 2.11/0.65    spl15_14 | spl15_19 | ~spl15_18),
% 2.11/0.65    inference(avatar_split_clause,[],[f959,f956,f962,f910])).
% 2.11/0.65  fof(f956,plain,(
% 2.11/0.65    spl15_18 <=> ! [X1] : ~r2_hidden(k4_tarski(sK0,sK1),k4_xboole_0(X1,k2_zfmisc_1(sK4,sK5)))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).
% 2.11/0.65  fof(f959,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | ~r2_hidden(k4_tarski(sK0,sK1),X0)) ) | ~spl15_18),
% 2.11/0.65    inference(resolution,[],[f957,f69])).
% 2.11/0.65  fof(f957,plain,(
% 2.11/0.65    ( ! [X1] : (~r2_hidden(k4_tarski(sK0,sK1),k4_xboole_0(X1,k2_zfmisc_1(sK4,sK5)))) ) | ~spl15_18),
% 2.11/0.65    inference(avatar_component_clause,[],[f956])).
% 2.11/0.65  fof(f958,plain,(
% 2.11/0.65    spl15_18 | spl15_16 | ~spl15_13),
% 2.11/0.65    inference(avatar_split_clause,[],[f950,f900,f923,f956])).
% 2.11/0.65  fof(f900,plain,(
% 2.11/0.65    spl15_13 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).
% 2.11/0.65  fof(f950,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r2_hidden(sK2,X0) | ~r2_hidden(k4_tarski(sK0,sK1),k4_xboole_0(X1,k2_zfmisc_1(sK4,sK5)))) ) | ~spl15_13),
% 2.11/0.65    inference(resolution,[],[f907,f153])).
% 2.11/0.65  fof(f907,plain,(
% 2.11/0.65    r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_zfmisc_1(sK4,sK5)) | ~spl15_13),
% 2.11/0.65    inference(resolution,[],[f902,f44])).
% 2.11/0.65  fof(f902,plain,(
% 2.11/0.65    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl15_13),
% 2.11/0.65    inference(avatar_component_clause,[],[f900])).
% 2.11/0.65  fof(f934,plain,(
% 2.11/0.65    ~spl15_16),
% 2.11/0.65    inference(avatar_contradiction_clause,[],[f930])).
% 2.11/0.65  fof(f930,plain,(
% 2.11/0.65    $false | ~spl15_16),
% 2.11/0.65    inference(resolution,[],[f924,f38])).
% 2.11/0.65  fof(f924,plain,(
% 2.11/0.65    ( ! [X2] : (~r2_hidden(sK2,X2)) ) | ~spl15_16),
% 2.11/0.65    inference(avatar_component_clause,[],[f923])).
% 2.11/0.65  fof(f915,plain,(
% 2.11/0.65    spl15_14 | spl15_15 | ~spl15_13),
% 2.11/0.65    inference(avatar_split_clause,[],[f908,f900,f913,f910])).
% 2.11/0.65  fof(f908,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r2_hidden(sK2,k4_xboole_0(X0,sK6)) | ~r2_hidden(k4_tarski(sK0,sK1),X1)) ) | ~spl15_13),
% 2.11/0.65    inference(resolution,[],[f906,f146])).
% 2.11/0.65  fof(f906,plain,(
% 2.11/0.65    r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),sK6) | ~spl15_13),
% 2.11/0.65    inference(resolution,[],[f902,f45])).
% 2.11/0.65  fof(f903,plain,(
% 2.11/0.65    spl15_6 | spl15_13 | ~spl15_12),
% 2.11/0.65    inference(avatar_split_clause,[],[f897,f848,f900,f207])).
% 2.11/0.65  fof(f207,plain,(
% 2.11/0.65    spl15_6 <=> ! [X14] : ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X14)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).
% 2.11/0.65  fof(f848,plain,(
% 2.11/0.65    spl15_12 <=> ! [X1] : ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_xboole_0(X1,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).
% 2.11/0.65  fof(f897,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X0)) ) | ~spl15_12),
% 2.11/0.65    inference(resolution,[],[f849,f69])).
% 2.11/0.65  fof(f849,plain,(
% 2.11/0.65    ( ! [X1] : (~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_xboole_0(X1,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)))) ) | ~spl15_12),
% 2.11/0.65    inference(avatar_component_clause,[],[f848])).
% 2.11/0.65  fof(f863,plain,(
% 2.11/0.65    ~spl15_8),
% 2.11/0.65    inference(avatar_contradiction_clause,[],[f859])).
% 2.11/0.65  fof(f859,plain,(
% 2.11/0.65    $false | ~spl15_8),
% 2.11/0.65    inference(resolution,[],[f225,f38])).
% 2.11/0.65  fof(f225,plain,(
% 2.11/0.65    ( ! [X0] : (~r2_hidden(sK3,X0)) ) | ~spl15_8),
% 2.11/0.65    inference(avatar_component_clause,[],[f224])).
% 2.11/0.65  fof(f224,plain,(
% 2.11/0.65    spl15_8 <=> ! [X0] : ~r2_hidden(sK3,X0)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).
% 2.11/0.65  fof(f850,plain,(
% 2.11/0.65    spl15_12 | spl15_8 | ~spl15_1),
% 2.11/0.65    inference(avatar_split_clause,[],[f836,f78,f224,f848])).
% 2.11/0.65  fof(f78,plain,(
% 2.11/0.65    spl15_1 <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 2.11/0.65  fof(f836,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r2_hidden(sK3,X0) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_xboole_0(X1,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)))) ) | ~spl15_1),
% 2.11/0.65    inference(resolution,[],[f153,f119])).
% 2.11/0.65  fof(f119,plain,(
% 2.11/0.65    r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl15_1),
% 2.11/0.65    inference(resolution,[],[f79,f44])).
% 2.11/0.65  fof(f79,plain,(
% 2.11/0.65    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | ~spl15_1),
% 2.11/0.65    inference(avatar_component_clause,[],[f78])).
% 2.11/0.65  fof(f226,plain,(
% 2.11/0.65    spl15_8 | spl15_5 | ~spl15_7),
% 2.11/0.65    inference(avatar_split_clause,[],[f217,f210,f94,f224])).
% 2.11/0.65  fof(f94,plain,(
% 2.11/0.65    spl15_5 <=> r2_hidden(sK3,sK7)),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).
% 2.11/0.65  fof(f210,plain,(
% 2.11/0.65    spl15_7 <=> ! [X13] : ~r2_hidden(sK3,k4_xboole_0(X13,sK7))),
% 2.11/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).
% 2.11/0.65  fof(f217,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(sK3,sK7) | ~r2_hidden(sK3,X0)) ) | ~spl15_7),
% 2.11/0.65    inference(resolution,[],[f211,f69])).
% 2.11/0.65  fof(f211,plain,(
% 2.11/0.65    ( ! [X13] : (~r2_hidden(sK3,k4_xboole_0(X13,sK7))) ) | ~spl15_7),
% 2.11/0.65    inference(avatar_component_clause,[],[f210])).
% 2.11/0.65  fof(f216,plain,(
% 2.11/0.65    ~spl15_6),
% 2.11/0.65    inference(avatar_contradiction_clause,[],[f214])).
% 2.11/0.65  fof(f214,plain,(
% 2.11/0.65    $false | ~spl15_6),
% 2.11/0.65    inference(resolution,[],[f208,f38])).
% 2.11/0.65  fof(f208,plain,(
% 2.11/0.65    ( ! [X14] : (~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X14)) ) | ~spl15_6),
% 2.11/0.65    inference(avatar_component_clause,[],[f207])).
% 2.11/0.65  fof(f212,plain,(
% 2.11/0.65    spl15_6 | spl15_7 | ~spl15_1),
% 2.11/0.65    inference(avatar_split_clause,[],[f198,f78,f210,f207])).
% 2.11/0.65  fof(f198,plain,(
% 2.11/0.65    ( ! [X14,X13] : (~r2_hidden(sK3,k4_xboole_0(X13,sK7)) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),X14)) ) | ~spl15_1),
% 2.11/0.65    inference(resolution,[],[f146,f118])).
% 2.11/0.65  fof(f118,plain,(
% 2.11/0.65    r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),sK7) | ~spl15_1),
% 2.11/0.65    inference(resolution,[],[f79,f45])).
% 2.11/0.65  fof(f115,plain,(
% 2.11/0.65    spl15_1 | ~spl15_2 | ~spl15_3 | ~spl15_4 | ~spl15_5),
% 2.11/0.65    inference(avatar_contradiction_clause,[],[f114])).
% 2.11/0.65  fof(f114,plain,(
% 2.11/0.65    $false | (spl15_1 | ~spl15_2 | ~spl15_3 | ~spl15_4 | ~spl15_5)),
% 2.11/0.65    inference(subsumption_resolution,[],[f113,f83])).
% 2.11/0.65  fof(f83,plain,(
% 2.11/0.65    r2_hidden(sK0,sK4) | ~spl15_2),
% 2.11/0.65    inference(avatar_component_clause,[],[f82])).
% 2.11/0.65  fof(f113,plain,(
% 2.11/0.65    ~r2_hidden(sK0,sK4) | (spl15_1 | ~spl15_3 | ~spl15_4 | ~spl15_5)),
% 2.11/0.65    inference(subsumption_resolution,[],[f112,f87])).
% 2.11/0.65  fof(f87,plain,(
% 2.11/0.65    r2_hidden(sK1,sK5) | ~spl15_3),
% 2.11/0.65    inference(avatar_component_clause,[],[f86])).
% 2.11/0.65  fof(f112,plain,(
% 2.11/0.65    ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | (spl15_1 | ~spl15_4 | ~spl15_5)),
% 2.11/0.65    inference(resolution,[],[f111,f73])).
% 2.11/0.65  fof(f111,plain,(
% 2.11/0.65    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | (spl15_1 | ~spl15_4 | ~spl15_5)),
% 2.11/0.65    inference(subsumption_resolution,[],[f110,f91])).
% 2.11/0.65  fof(f91,plain,(
% 2.11/0.65    r2_hidden(sK2,sK6) | ~spl15_4),
% 2.11/0.65    inference(avatar_component_clause,[],[f90])).
% 2.11/0.65  fof(f110,plain,(
% 2.11/0.65    ~r2_hidden(sK2,sK6) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | (spl15_1 | ~spl15_5)),
% 2.11/0.65    inference(resolution,[],[f109,f73])).
% 2.11/0.65  fof(f109,plain,(
% 2.11/0.65    ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | (spl15_1 | ~spl15_5)),
% 2.11/0.65    inference(subsumption_resolution,[],[f104,f95])).
% 2.11/0.65  fof(f95,plain,(
% 2.11/0.65    r2_hidden(sK3,sK7) | ~spl15_5),
% 2.11/0.65    inference(avatar_component_clause,[],[f94])).
% 2.11/0.65  fof(f104,plain,(
% 2.11/0.65    ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl15_1),
% 2.11/0.65    inference(resolution,[],[f73,f80])).
% 2.11/0.65  fof(f80,plain,(
% 2.11/0.65    ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | spl15_1),
% 2.11/0.65    inference(avatar_component_clause,[],[f78])).
% 2.11/0.65  fof(f101,plain,(
% 2.11/0.65    spl15_1 | spl15_2),
% 2.11/0.65    inference(avatar_split_clause,[],[f68,f82,f78])).
% 2.11/0.65  fof(f68,plain,(
% 2.11/0.65    r2_hidden(sK0,sK4) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.11/0.65    inference(definition_unfolding,[],[f33,f63,f62])).
% 2.11/0.65  fof(f62,plain,(
% 2.11/0.65    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.11/0.65    inference(definition_unfolding,[],[f61,f43])).
% 2.11/0.65  fof(f43,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f5])).
% 2.11/0.65  fof(f5,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.11/0.65  fof(f61,plain,(
% 2.11/0.65    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f7])).
% 2.11/0.65  fof(f7,axiom,(
% 2.11/0.65    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.11/0.65  fof(f63,plain,(
% 2.11/0.65    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 2.11/0.65    inference(definition_unfolding,[],[f60,f42])).
% 2.11/0.65  fof(f42,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f4])).
% 2.11/0.65  fof(f4,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.11/0.65  fof(f60,plain,(
% 2.11/0.65    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f6])).
% 2.11/0.65  fof(f6,axiom,(
% 2.11/0.65    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 2.11/0.65  fof(f33,plain,(
% 2.11/0.65    r2_hidden(sK0,sK4) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.11/0.65    inference(cnf_transformation,[],[f19])).
% 2.11/0.65  fof(f19,plain,(
% 2.11/0.65    (~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))) & ((r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5) & r2_hidden(sK0,sK4)) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f17,f18])).
% 2.11/0.65  fof(f18,plain,(
% 2.11/0.65    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)))) => ((~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))) & ((r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5) & r2_hidden(sK0,sK4)) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f17,plain,(
% 2.11/0.65    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 2.11/0.65    inference(flattening,[],[f16])).
% 2.11/0.65  fof(f16,plain,(
% 2.11/0.65    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4)) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 2.11/0.65    inference(nnf_transformation,[],[f12])).
% 2.11/0.65  fof(f12,plain,(
% 2.11/0.65    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <~> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 2.11/0.65    inference(ennf_transformation,[],[f10])).
% 2.11/0.65  fof(f10,negated_conjecture,(
% 2.11/0.65    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 2.11/0.65    inference(negated_conjecture,[],[f9])).
% 2.11/0.65  fof(f9,conjecture,(
% 2.11/0.65    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).
% 2.11/0.65  fof(f100,plain,(
% 2.11/0.65    spl15_1 | spl15_3),
% 2.11/0.65    inference(avatar_split_clause,[],[f67,f86,f78])).
% 2.11/0.65  fof(f67,plain,(
% 2.11/0.65    r2_hidden(sK1,sK5) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.11/0.65    inference(definition_unfolding,[],[f34,f63,f62])).
% 2.11/0.65  fof(f34,plain,(
% 2.11/0.65    r2_hidden(sK1,sK5) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.11/0.65    inference(cnf_transformation,[],[f19])).
% 2.11/0.65  fof(f99,plain,(
% 2.11/0.65    spl15_1 | spl15_4),
% 2.11/0.65    inference(avatar_split_clause,[],[f66,f90,f78])).
% 2.11/0.65  fof(f66,plain,(
% 2.11/0.65    r2_hidden(sK2,sK6) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.11/0.65    inference(definition_unfolding,[],[f35,f63,f62])).
% 2.11/0.65  fof(f35,plain,(
% 2.11/0.65    r2_hidden(sK2,sK6) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.11/0.65    inference(cnf_transformation,[],[f19])).
% 2.11/0.65  fof(f98,plain,(
% 2.11/0.65    spl15_1 | spl15_5),
% 2.11/0.65    inference(avatar_split_clause,[],[f65,f94,f78])).
% 2.11/0.65  fof(f65,plain,(
% 2.11/0.65    r2_hidden(sK3,sK7) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.11/0.65    inference(definition_unfolding,[],[f36,f63,f62])).
% 2.11/0.65  fof(f36,plain,(
% 2.11/0.65    r2_hidden(sK3,sK7) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.11/0.65    inference(cnf_transformation,[],[f19])).
% 2.11/0.65  fof(f97,plain,(
% 2.11/0.65    ~spl15_1 | ~spl15_2 | ~spl15_3 | ~spl15_4 | ~spl15_5),
% 2.11/0.65    inference(avatar_split_clause,[],[f64,f94,f90,f86,f82,f78])).
% 2.11/0.65  fof(f64,plain,(
% 2.11/0.65    ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.11/0.65    inference(definition_unfolding,[],[f37,f63,f62])).
% 2.11/0.65  fof(f37,plain,(
% 2.11/0.65    ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.11/0.65    inference(cnf_transformation,[],[f19])).
% 2.11/0.65  % SZS output end Proof for theBenchmark
% 2.11/0.65  % (28041)------------------------------
% 2.11/0.65  % (28041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.65  % (28041)Termination reason: Refutation
% 2.11/0.65  
% 2.11/0.65  % (28041)Memory used [KB]: 11513
% 2.11/0.65  % (28041)Time elapsed: 0.242 s
% 2.11/0.65  % (28041)------------------------------
% 2.11/0.65  % (28041)------------------------------
% 2.11/0.65  % (28037)Success in time 0.289 s
%------------------------------------------------------------------------------
