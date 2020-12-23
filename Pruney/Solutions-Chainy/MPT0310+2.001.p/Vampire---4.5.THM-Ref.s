%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:06 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 535 expanded)
%              Number of leaves         :   38 ( 214 expanded)
%              Depth                    :   11
%              Number of atoms          :  623 (2470 expanded)
%              Number of equality atoms :   78 ( 381 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f157,f206,f229,f235,f387,f581,f1015,f1034,f1060,f1061,f1082,f1083,f1090,f1169,f1243,f1245,f1247,f1250,f1251,f1255,f1263,f1279,f1336,f1337,f1486,f1517,f1518,f1546,f1569,f1571,f1595,f1597,f1599,f1654,f1655])).

fof(f1655,plain,
    ( spl13_36
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f1557,f382,f578])).

fof(f578,plain,
    ( spl13_36
  <=> r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f382,plain,
    ( spl13_30
  <=> r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f1557,plain,
    ( r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1)
    | ~ spl13_30 ),
    inference(resolution,[],[f383,f88])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f383,plain,
    ( r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f382])).

fof(f1654,plain,
    ( ~ spl13_29
    | ~ spl13_36
    | spl13_34 ),
    inference(avatar_split_clause,[],[f1644,f431,f578,f378])).

fof(f378,plain,
    ( spl13_29
  <=> r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).

fof(f431,plain,
    ( spl13_34
  <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f1644,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2)
    | spl13_34 ),
    inference(resolution,[],[f433,f91])).

fof(f91,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
              & r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
                & r2_hidden(sK9(X0,X1,X8),X1)
                & r2_hidden(sK8(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f32,f35,f34,f33])).

fof(f33,plain,(
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
              ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
        & r2_hidden(sK9(X0,X1,X8),X1)
        & r2_hidden(sK8(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f433,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1))
    | spl13_34 ),
    inference(avatar_component_clause,[],[f431])).

fof(f1599,plain,
    ( spl13_29
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f1498,f431,f378])).

fof(f1498,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2)
    | ~ spl13_34 ),
    inference(resolution,[],[f432,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f432,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1))
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f431])).

fof(f1597,plain,
    ( spl13_29
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f1526,f198,f378])).

fof(f198,plain,
    ( spl13_19
  <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f1526,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2)
    | ~ spl13_19 ),
    inference(resolution,[],[f200,f72])).

fof(f200,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f198])).

fof(f1595,plain,
    ( ~ spl13_29
    | ~ spl13_35
    | spl13_33 ),
    inference(avatar_split_clause,[],[f1585,f427,f574,f378])).

fof(f574,plain,
    ( spl13_35
  <=> r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f427,plain,
    ( spl13_33
  <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f1585,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0)
    | ~ r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2)
    | spl13_33 ),
    inference(resolution,[],[f429,f91])).

fof(f429,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0))
    | spl13_33 ),
    inference(avatar_component_clause,[],[f427])).

fof(f1571,plain,
    ( ~ spl13_33
    | ~ spl13_34
    | spl13_20 ),
    inference(avatar_split_clause,[],[f418,f202,f431,f427])).

fof(f202,plain,
    ( spl13_20
  <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f418,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0))
    | spl13_20 ),
    inference(resolution,[],[f203,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f46])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f203,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))
    | spl13_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f1569,plain,
    ( spl13_35
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f1556,f382,f574])).

fof(f1556,plain,
    ( r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0)
    | ~ spl13_30 ),
    inference(resolution,[],[f383,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f46])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1546,plain,
    ( spl13_30
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f1529,f198,f382])).

fof(f1529,plain,
    ( r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl13_19 ),
    inference(resolution,[],[f200,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f1518,plain,
    ( spl13_17
    | spl13_18
    | spl13_19
    | spl13_2
    | spl13_20 ),
    inference(avatar_split_clause,[],[f417,f202,f114,f198,f195,f192])).

fof(f192,plain,
    ( spl13_17
  <=> ! [X5,X4] : ~ r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_zfmisc_1(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f195,plain,
    ( spl13_18
  <=> ! [X3,X2] : ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f114,plain,
    ( spl13_2
  <=> sQ12_eqProxy(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f417,plain,
    ( ! [X2,X0,X3,X1] :
        ( sQ12_eqProxy(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))
        | r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
        | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X0,X1))
        | ~ r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_zfmisc_1(X2,X3)) )
    | spl13_20 ),
    inference(resolution,[],[f203,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sQ12_eqProxy(X0,X3)
      | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3)
      | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f75,f95])).

fof(f95,plain,(
    ! [X1,X0] :
      ( sQ12_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3)
      | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ( ( ~ r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0) )
        & ( r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3)
          | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0) ) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f41,f42])).

fof(f42,plain,(
    ! [X3,X0] :
      ( ? [X6,X7] :
          ( ( ~ r2_hidden(k4_tarski(X6,X7),X3)
            | ~ r2_hidden(k4_tarski(X6,X7),X0) )
          & ( r2_hidden(k4_tarski(X6,X7),X3)
            | r2_hidden(k4_tarski(X6,X7),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0) )
        & ( r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3)
          | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( ( ~ r2_hidden(k4_tarski(X6,X7),X3)
            | ~ r2_hidden(k4_tarski(X6,X7),X0) )
          & ( r2_hidden(k4_tarski(X6,X7),X3)
            | r2_hidden(k4_tarski(X6,X7),X0) ) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( r2_hidden(k4_tarski(X6,X7),X0)
        <~> r2_hidden(k4_tarski(X6,X7),X3) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( r2_hidden(k4_tarski(X6,X7),X0)
        <~> r2_hidden(k4_tarski(X6,X7),X3) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ! [X6,X7] :
            ( r2_hidden(k4_tarski(X6,X7),X0)
          <=> r2_hidden(k4_tarski(X6,X7),X3) )
        & r1_tarski(X3,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
     => X0 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l130_zfmisc_1)).

fof(f1517,plain,
    ( spl13_36
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f1501,f431,f578])).

fof(f1501,plain,
    ( r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1)
    | ~ spl13_34 ),
    inference(resolution,[],[f432,f70])).

fof(f1486,plain,
    ( spl13_35
    | ~ spl13_33 ),
    inference(avatar_split_clause,[],[f1468,f427,f574])).

fof(f1468,plain,
    ( r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0)
    | ~ spl13_33 ),
    inference(resolution,[],[f428,f70])).

fof(f428,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0))
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f427])).

fof(f1337,plain,
    ( spl13_34
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f1323,f202,f431])).

fof(f1323,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1))
    | ~ spl13_20 ),
    inference(resolution,[],[f204,f88])).

fof(f204,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f1336,plain,
    ( spl13_33
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f1322,f202,f427])).

fof(f1322,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0))
    | ~ spl13_20 ),
    inference(resolution,[],[f204,f89])).

fof(f1279,plain,(
    ~ spl13_18 ),
    inference(avatar_contradiction_clause,[],[f1276])).

fof(f1276,plain,
    ( $false
    | ~ spl13_18 ),
    inference(resolution,[],[f196,f78])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f196,plain,
    ( ! [X2,X3] : ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X2,X3))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f1263,plain,(
    ~ spl13_17 ),
    inference(avatar_contradiction_clause,[],[f1258])).

fof(f1258,plain,
    ( $false
    | ~ spl13_17 ),
    inference(resolution,[],[f193,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f193,plain,
    ( ! [X4,X5] : ~ r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_zfmisc_1(X4,X5))
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f1255,plain,
    ( spl13_7
    | spl13_8
    | spl13_10
    | spl13_1
    | spl13_9 ),
    inference(avatar_split_clause,[],[f1038,f149,f110,f153,f146,f143])).

fof(f143,plain,
    ( spl13_7
  <=> ! [X5,X4] : ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k2_zfmisc_1(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f146,plain,
    ( spl13_8
  <=> ! [X3,X2] : ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f153,plain,
    ( spl13_10
  <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f110,plain,
    ( spl13_1
  <=> sQ12_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f149,plain,
    ( spl13_9
  <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f1038,plain,
    ( ! [X2,X0,X3,X1] :
        ( sQ12_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))
        | r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))
        | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X0,X1))
        | ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k2_zfmisc_1(X2,X3)) )
    | spl13_9 ),
    inference(resolution,[],[f150,f107])).

fof(f150,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2))
    | spl13_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f1251,plain,
    ( spl13_42
    | ~ spl13_9 ),
    inference(avatar_split_clause,[],[f348,f149,f1010])).

fof(f1010,plain,
    ( spl13_42
  <=> r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f348,plain,
    ( r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2)
    | ~ spl13_9 ),
    inference(resolution,[],[f151,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f151,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2))
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f1250,plain,
    ( ~ spl13_44
    | ~ spl13_42
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1018,f413,f1010,f1166])).

fof(f1166,plain,
    ( spl13_44
  <=> r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f413,plain,
    ( spl13_32
  <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f1018,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1)
    | spl13_32 ),
    inference(resolution,[],[f415,f91])).

fof(f415,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2))
    | spl13_32 ),
    inference(avatar_component_clause,[],[f413])).

fof(f1247,plain,
    ( ~ spl13_31
    | ~ spl13_32
    | spl13_10 ),
    inference(avatar_split_clause,[],[f400,f153,f413,f409])).

fof(f409,plain,
    ( spl13_31
  <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_31])])).

fof(f400,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2))
    | spl13_10 ),
    inference(resolution,[],[f154,f87])).

fof(f154,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))
    | spl13_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f1245,plain,
    ( spl13_44
    | ~ spl13_9 ),
    inference(avatar_split_clause,[],[f553,f149,f1166])).

fof(f553,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1)
    | ~ spl13_9 ),
    inference(resolution,[],[f347,f88])).

fof(f347,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl13_9 ),
    inference(resolution,[],[f151,f72])).

fof(f1243,plain,
    ( spl13_44
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f1226,f413,f1166])).

fof(f1226,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1)
    | ~ spl13_32 ),
    inference(resolution,[],[f414,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f414,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2))
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f413])).

fof(f1169,plain,
    ( ~ spl13_41
    | ~ spl13_44
    | spl13_43 ),
    inference(avatar_split_clause,[],[f1157,f1085,f1166,f1006])).

fof(f1006,plain,
    ( spl13_41
  <=> r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).

fof(f1085,plain,
    ( spl13_43
  <=> r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_43])])).

fof(f1157,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1)
    | ~ r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0)
    | spl13_43 ),
    inference(resolution,[],[f1087,f87])).

fof(f1087,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl13_43 ),
    inference(avatar_component_clause,[],[f1085])).

fof(f1090,plain,
    ( ~ spl13_43
    | ~ spl13_42
    | spl13_9 ),
    inference(avatar_split_clause,[],[f1035,f149,f1010,f1085])).

fof(f1035,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl13_9 ),
    inference(resolution,[],[f150,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1083,plain,
    ( spl13_42
    | ~ spl13_31 ),
    inference(avatar_split_clause,[],[f1065,f409,f1010])).

fof(f1065,plain,
    ( r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2)
    | ~ spl13_31 ),
    inference(resolution,[],[f410,f70])).

fof(f410,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2))
    | ~ spl13_31 ),
    inference(avatar_component_clause,[],[f409])).

fof(f1082,plain,
    ( spl13_41
    | ~ spl13_31 ),
    inference(avatar_split_clause,[],[f1064,f409,f1006])).

fof(f1064,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0)
    | ~ spl13_31 ),
    inference(resolution,[],[f410,f69])).

fof(f1061,plain,
    ( spl13_32
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f1047,f153,f413])).

fof(f1047,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2))
    | ~ spl13_10 ),
    inference(resolution,[],[f155,f88])).

fof(f155,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f1060,plain,
    ( spl13_31
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f1046,f153,f409])).

fof(f1046,plain,
    ( r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2))
    | ~ spl13_10 ),
    inference(resolution,[],[f155,f89])).

fof(f1034,plain,
    ( ~ spl13_9
    | spl13_41 ),
    inference(avatar_contradiction_clause,[],[f1026])).

fof(f1026,plain,
    ( $false
    | ~ spl13_9
    | spl13_41 ),
    inference(resolution,[],[f1008,f552])).

fof(f552,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0)
    | ~ spl13_9 ),
    inference(resolution,[],[f347,f89])).

fof(f1008,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0)
    | spl13_41 ),
    inference(avatar_component_clause,[],[f1006])).

fof(f1015,plain,
    ( ~ spl13_41
    | ~ spl13_42
    | spl13_31 ),
    inference(avatar_split_clause,[],[f997,f409,f1010,f1006])).

fof(f997,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0)
    | spl13_31 ),
    inference(resolution,[],[f411,f91])).

fof(f411,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2))
    | spl13_31 ),
    inference(avatar_component_clause,[],[f409])).

fof(f581,plain,
    ( ~ spl13_35
    | ~ spl13_36
    | spl13_30 ),
    inference(avatar_split_clause,[],[f565,f382,f578,f574])).

fof(f565,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0)
    | spl13_30 ),
    inference(resolution,[],[f384,f87])).

fof(f384,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl13_30 ),
    inference(avatar_component_clause,[],[f382])).

fof(f387,plain,
    ( ~ spl13_29
    | ~ spl13_30
    | spl13_19 ),
    inference(avatar_split_clause,[],[f368,f198,f382,f378])).

fof(f368,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2)
    | spl13_19 ),
    inference(resolution,[],[f199,f91])).

fof(f199,plain,
    ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl13_19 ),
    inference(avatar_component_clause,[],[f198])).

fof(f235,plain,(
    ~ spl13_8 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl13_8 ),
    inference(resolution,[],[f147,f78])).

fof(f147,plain,
    ( ! [X2,X3] : ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X2,X3))
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f229,plain,(
    ~ spl13_7 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl13_7 ),
    inference(resolution,[],[f144,f86])).

fof(f144,plain,
    ( ! [X4,X5] : ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k2_zfmisc_1(X4,X5))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f206,plain,
    ( spl13_17
    | spl13_18
    | ~ spl13_19
    | ~ spl13_20
    | spl13_2 ),
    inference(avatar_split_clause,[],[f171,f114,f202,f198,f195,f192])).

fof(f171,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))
        | ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
        | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X6,X7))
        | ~ r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_zfmisc_1(X8,X9)) )
    | spl13_2 ),
    inference(resolution,[],[f116,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sQ12_eqProxy(X0,X3)
      | ~ r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3)
      | ~ r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f76,f95])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3)
      | ~ r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f116,plain,
    ( ~ sQ12_eqProxy(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f157,plain,
    ( spl13_7
    | spl13_8
    | ~ spl13_9
    | ~ spl13_10
    | spl13_1 ),
    inference(avatar_split_clause,[],[f122,f110,f153,f149,f146,f143])).

fof(f122,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))
        | ~ r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2))
        | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X6,X7))
        | ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k2_zfmisc_1(X8,X9)) )
    | spl13_1 ),
    inference(resolution,[],[f112,f106])).

fof(f112,plain,
    ( ~ sQ12_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f117,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f96,f114,f110])).

fof(f96,plain,
    ( ~ sQ12_eqProxy(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))
    | ~ sQ12_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) ),
    inference(equality_proxy_replacement,[],[f77,f95,f95])).

fof(f77,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))
    | k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))) ),
    inference(definition_unfolding,[],[f44,f46,f46,f46,f46])).

fof(f44,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | k2_zfmisc_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
   => ( k2_zfmisc_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
      | k2_zfmisc_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | k2_zfmisc_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:41:30 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.22/0.51  % (8921)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (8917)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (8938)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (8930)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (8924)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (8920)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (8920)Refutation not found, incomplete strategy% (8920)------------------------------
% 0.22/0.53  % (8920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8929)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (8919)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (8922)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (8932)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (8916)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (8939)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (8942)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (8918)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (8934)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (8940)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (8918)Refutation not found, incomplete strategy% (8918)------------------------------
% 0.22/0.54  % (8918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8918)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8918)Memory used [KB]: 10746
% 0.22/0.54  % (8918)Time elapsed: 0.135 s
% 0.22/0.54  % (8918)------------------------------
% 0.22/0.54  % (8918)------------------------------
% 0.22/0.54  % (8943)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (8944)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (8931)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (8933)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (8945)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (8920)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8920)Memory used [KB]: 6268
% 0.22/0.54  % (8920)Time elapsed: 0.127 s
% 0.22/0.54  % (8920)------------------------------
% 0.22/0.54  % (8920)------------------------------
% 0.22/0.55  % (8927)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (8935)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (8924)Refutation not found, incomplete strategy% (8924)------------------------------
% 0.22/0.55  % (8924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8924)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8924)Memory used [KB]: 10746
% 0.22/0.55  % (8924)Time elapsed: 0.142 s
% 0.22/0.55  % (8924)------------------------------
% 0.22/0.55  % (8924)------------------------------
% 0.22/0.55  % (8936)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (8923)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (8936)Refutation not found, incomplete strategy% (8936)------------------------------
% 0.22/0.55  % (8936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8936)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8936)Memory used [KB]: 10746
% 0.22/0.55  % (8936)Time elapsed: 0.149 s
% 0.22/0.55  % (8936)------------------------------
% 0.22/0.55  % (8936)------------------------------
% 0.22/0.55  % (8937)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (8928)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (8937)Refutation not found, incomplete strategy% (8937)------------------------------
% 0.22/0.55  % (8937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8937)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8937)Memory used [KB]: 1663
% 0.22/0.55  % (8937)Time elapsed: 0.115 s
% 0.22/0.55  % (8937)------------------------------
% 0.22/0.55  % (8937)------------------------------
% 0.22/0.55  % (8926)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (8925)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (8926)Refutation not found, incomplete strategy% (8926)------------------------------
% 0.22/0.55  % (8926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8926)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8926)Memory used [KB]: 10618
% 0.22/0.55  % (8926)Time elapsed: 0.149 s
% 0.22/0.55  % (8926)------------------------------
% 0.22/0.55  % (8926)------------------------------
% 0.22/0.56  % (8941)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (8941)Refutation not found, incomplete strategy% (8941)------------------------------
% 0.22/0.56  % (8941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8941)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8941)Memory used [KB]: 6268
% 0.22/0.56  % (8941)Time elapsed: 0.147 s
% 0.22/0.56  % (8941)------------------------------
% 0.22/0.56  % (8941)------------------------------
% 1.68/0.61  % (8931)Refutation found. Thanks to Tanya!
% 1.68/0.61  % SZS status Theorem for theBenchmark
% 1.68/0.61  % SZS output start Proof for theBenchmark
% 1.68/0.63  fof(f1656,plain,(
% 1.68/0.63    $false),
% 1.68/0.63    inference(avatar_sat_refutation,[],[f117,f157,f206,f229,f235,f387,f581,f1015,f1034,f1060,f1061,f1082,f1083,f1090,f1169,f1243,f1245,f1247,f1250,f1251,f1255,f1263,f1279,f1336,f1337,f1486,f1517,f1518,f1546,f1569,f1571,f1595,f1597,f1599,f1654,f1655])).
% 1.68/0.63  fof(f1655,plain,(
% 1.68/0.63    spl13_36 | ~spl13_30),
% 1.68/0.63    inference(avatar_split_clause,[],[f1557,f382,f578])).
% 1.68/0.63  fof(f578,plain,(
% 1.68/0.63    spl13_36 <=> r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).
% 1.68/0.63  fof(f382,plain,(
% 1.68/0.63    spl13_30 <=> r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).
% 1.68/0.63  fof(f1557,plain,(
% 1.68/0.63    r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1) | ~spl13_30),
% 1.68/0.63    inference(resolution,[],[f383,f88])).
% 1.68/0.63  fof(f88,plain,(
% 1.68/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.68/0.63    inference(equality_resolution,[],[f83])).
% 1.68/0.63  fof(f83,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.68/0.63    inference(definition_unfolding,[],[f56,f46])).
% 1.68/0.63  fof(f46,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f5])).
% 1.68/0.63  fof(f5,axiom,(
% 1.68/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.68/0.63  fof(f56,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.68/0.63    inference(cnf_transformation,[],[f30])).
% 1.68/0.63  fof(f30,plain,(
% 1.68/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.68/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.68/0.63  fof(f29,plain,(
% 1.68/0.63    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f28,plain,(
% 1.68/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.68/0.63    inference(rectify,[],[f27])).
% 1.68/0.63  fof(f27,plain,(
% 1.68/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.68/0.63    inference(flattening,[],[f26])).
% 1.68/0.63  fof(f26,plain,(
% 1.68/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.68/0.63    inference(nnf_transformation,[],[f2])).
% 1.68/0.63  fof(f2,axiom,(
% 1.68/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.68/0.63  fof(f383,plain,(
% 1.68/0.63    r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl13_30),
% 1.68/0.63    inference(avatar_component_clause,[],[f382])).
% 1.68/0.63  fof(f1654,plain,(
% 1.68/0.63    ~spl13_29 | ~spl13_36 | spl13_34),
% 1.68/0.63    inference(avatar_split_clause,[],[f1644,f431,f578,f378])).
% 1.68/0.63  fof(f378,plain,(
% 1.68/0.63    spl13_29 <=> r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).
% 1.68/0.63  fof(f431,plain,(
% 1.68/0.63    spl13_34 <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).
% 1.68/0.63  fof(f1644,plain,(
% 1.68/0.63    ~r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1) | ~r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2) | spl13_34),
% 1.68/0.63    inference(resolution,[],[f433,f91])).
% 1.68/0.63  fof(f91,plain,(
% 1.68/0.63    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.68/0.63    inference(equality_resolution,[],[f90])).
% 1.68/0.63  fof(f90,plain,(
% 1.68/0.63    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.68/0.63    inference(equality_resolution,[],[f64])).
% 1.68/0.63  fof(f64,plain,(
% 1.68/0.63    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.68/0.63    inference(cnf_transformation,[],[f36])).
% 1.68/0.63  fof(f36,plain,(
% 1.68/0.63    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.68/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f32,f35,f34,f33])).
% 1.68/0.63  fof(f33,plain,(
% 1.68/0.63    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f34,plain,(
% 1.68/0.63    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f35,plain,(
% 1.68/0.63    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f32,plain,(
% 1.68/0.63    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.68/0.63    inference(rectify,[],[f31])).
% 1.68/0.63  fof(f31,plain,(
% 1.68/0.63    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.68/0.63    inference(nnf_transformation,[],[f6])).
% 1.68/0.63  fof(f6,axiom,(
% 1.68/0.63    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.68/0.63  fof(f433,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1)) | spl13_34),
% 1.68/0.63    inference(avatar_component_clause,[],[f431])).
% 1.68/0.63  fof(f1599,plain,(
% 1.68/0.63    spl13_29 | ~spl13_34),
% 1.68/0.63    inference(avatar_split_clause,[],[f1498,f431,f378])).
% 1.68/0.63  fof(f1498,plain,(
% 1.68/0.63    r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2) | ~spl13_34),
% 1.68/0.63    inference(resolution,[],[f432,f72])).
% 1.68/0.63  fof(f72,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f40])).
% 1.68/0.63  fof(f40,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.68/0.63    inference(flattening,[],[f39])).
% 1.68/0.63  fof(f39,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.68/0.63    inference(nnf_transformation,[],[f8])).
% 1.68/0.63  fof(f8,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.68/0.63  fof(f432,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1)) | ~spl13_34),
% 1.68/0.63    inference(avatar_component_clause,[],[f431])).
% 1.68/0.63  fof(f1597,plain,(
% 1.68/0.63    spl13_29 | ~spl13_19),
% 1.68/0.63    inference(avatar_split_clause,[],[f1526,f198,f378])).
% 1.68/0.63  fof(f198,plain,(
% 1.68/0.63    spl13_19 <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 1.68/0.63  fof(f1526,plain,(
% 1.68/0.63    r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2) | ~spl13_19),
% 1.68/0.63    inference(resolution,[],[f200,f72])).
% 1.68/0.63  fof(f200,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl13_19),
% 1.68/0.63    inference(avatar_component_clause,[],[f198])).
% 1.68/0.63  fof(f1595,plain,(
% 1.68/0.63    ~spl13_29 | ~spl13_35 | spl13_33),
% 1.68/0.63    inference(avatar_split_clause,[],[f1585,f427,f574,f378])).
% 1.68/0.63  fof(f574,plain,(
% 1.68/0.63    spl13_35 <=> r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).
% 1.68/0.63  fof(f427,plain,(
% 1.68/0.63    spl13_33 <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).
% 1.68/0.63  fof(f1585,plain,(
% 1.68/0.63    ~r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0) | ~r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2) | spl13_33),
% 1.68/0.63    inference(resolution,[],[f429,f91])).
% 1.68/0.63  fof(f429,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0)) | spl13_33),
% 1.68/0.63    inference(avatar_component_clause,[],[f427])).
% 1.68/0.63  fof(f1571,plain,(
% 1.68/0.63    ~spl13_33 | ~spl13_34 | spl13_20),
% 1.68/0.63    inference(avatar_split_clause,[],[f418,f202,f431,f427])).
% 1.68/0.63  fof(f202,plain,(
% 1.68/0.63    spl13_20 <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).
% 1.68/0.63  fof(f418,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0)) | spl13_20),
% 1.68/0.63    inference(resolution,[],[f203,f87])).
% 1.68/0.63  fof(f87,plain,(
% 1.68/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.68/0.63    inference(equality_resolution,[],[f82])).
% 1.68/0.63  fof(f82,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.68/0.63    inference(definition_unfolding,[],[f57,f46])).
% 1.68/0.63  fof(f57,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.68/0.63    inference(cnf_transformation,[],[f30])).
% 1.68/0.63  fof(f203,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))) | spl13_20),
% 1.68/0.63    inference(avatar_component_clause,[],[f202])).
% 1.68/0.63  fof(f1569,plain,(
% 1.68/0.63    spl13_35 | ~spl13_30),
% 1.68/0.63    inference(avatar_split_clause,[],[f1556,f382,f574])).
% 1.68/0.63  fof(f1556,plain,(
% 1.68/0.63    r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0) | ~spl13_30),
% 1.68/0.63    inference(resolution,[],[f383,f89])).
% 1.68/0.63  fof(f89,plain,(
% 1.68/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.68/0.63    inference(equality_resolution,[],[f84])).
% 1.68/0.63  fof(f84,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.68/0.63    inference(definition_unfolding,[],[f55,f46])).
% 1.68/0.63  fof(f55,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.68/0.63    inference(cnf_transformation,[],[f30])).
% 1.68/0.63  fof(f1546,plain,(
% 1.68/0.63    spl13_30 | ~spl13_19),
% 1.68/0.63    inference(avatar_split_clause,[],[f1529,f198,f382])).
% 1.68/0.63  fof(f1529,plain,(
% 1.68/0.63    r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl13_19),
% 1.68/0.63    inference(resolution,[],[f200,f70])).
% 1.68/0.63  fof(f70,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f38])).
% 1.68/0.63  fof(f38,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.68/0.63    inference(flattening,[],[f37])).
% 1.68/0.63  fof(f37,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.68/0.63    inference(nnf_transformation,[],[f9])).
% 1.68/0.63  fof(f9,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 1.68/0.63  fof(f1518,plain,(
% 1.68/0.63    spl13_17 | spl13_18 | spl13_19 | spl13_2 | spl13_20),
% 1.68/0.63    inference(avatar_split_clause,[],[f417,f202,f114,f198,f195,f192])).
% 1.68/0.63  fof(f192,plain,(
% 1.68/0.63    spl13_17 <=> ! [X5,X4] : ~r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_zfmisc_1(X4,X5))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 1.68/0.63  fof(f195,plain,(
% 1.68/0.63    spl13_18 <=> ! [X3,X2] : ~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X2,X3))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 1.68/0.63  fof(f114,plain,(
% 1.68/0.63    spl13_2 <=> sQ12_eqProxy(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.68/0.63  fof(f417,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (sQ12_eqProxy(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))) | r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_zfmisc_1(X2,X3))) ) | spl13_20),
% 1.68/0.63    inference(resolution,[],[f203,f107])).
% 1.68/0.63  fof(f107,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (sQ12_eqProxy(X0,X3) | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3) | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0) | ~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 1.68/0.63    inference(equality_proxy_replacement,[],[f75,f95])).
% 1.68/0.63  fof(f95,plain,(
% 1.68/0.63    ! [X1,X0] : (sQ12_eqProxy(X0,X1) <=> X0 = X1)),
% 1.68/0.63    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).
% 1.68/0.63  fof(f75,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3) | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0) | ~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f43])).
% 1.68/0.63  fof(f43,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5] : (X0 = X3 | ((~r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3) | ~r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0)) & (r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3) | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0))) | ~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.68/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f41,f42])).
% 1.68/0.63  fof(f42,plain,(
% 1.68/0.63    ! [X3,X0] : (? [X6,X7] : ((~r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X0)) & (r2_hidden(k4_tarski(X6,X7),X3) | r2_hidden(k4_tarski(X6,X7),X0))) => ((~r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3) | ~r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0)) & (r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3) | r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0))))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f41,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5] : (X0 = X3 | ? [X6,X7] : ((~r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X0)) & (r2_hidden(k4_tarski(X6,X7),X3) | r2_hidden(k4_tarski(X6,X7),X0))) | ~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.68/0.63    inference(nnf_transformation,[],[f17])).
% 1.68/0.63  fof(f17,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5] : (X0 = X3 | ? [X6,X7] : (r2_hidden(k4_tarski(X6,X7),X0) <~> r2_hidden(k4_tarski(X6,X7),X3)) | ~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.68/0.63    inference(flattening,[],[f16])).
% 1.68/0.63  fof(f16,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5] : (X0 = X3 | (? [X6,X7] : (r2_hidden(k4_tarski(X6,X7),X0) <~> r2_hidden(k4_tarski(X6,X7),X3)) | ~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))))),
% 1.68/0.63    inference(ennf_transformation,[],[f7])).
% 1.68/0.63  fof(f7,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5] : ((! [X6,X7] : (r2_hidden(k4_tarski(X6,X7),X0) <=> r2_hidden(k4_tarski(X6,X7),X3)) & r1_tarski(X3,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X1,X2))) => X0 = X3)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l130_zfmisc_1)).
% 1.68/0.63  fof(f1517,plain,(
% 1.68/0.63    spl13_36 | ~spl13_34),
% 1.68/0.63    inference(avatar_split_clause,[],[f1501,f431,f578])).
% 1.68/0.63  fof(f1501,plain,(
% 1.68/0.63    r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1) | ~spl13_34),
% 1.68/0.63    inference(resolution,[],[f432,f70])).
% 1.68/0.63  fof(f1486,plain,(
% 1.68/0.63    spl13_35 | ~spl13_33),
% 1.68/0.63    inference(avatar_split_clause,[],[f1468,f427,f574])).
% 1.68/0.63  fof(f1468,plain,(
% 1.68/0.63    r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0) | ~spl13_33),
% 1.68/0.63    inference(resolution,[],[f428,f70])).
% 1.68/0.63  fof(f428,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0)) | ~spl13_33),
% 1.68/0.63    inference(avatar_component_clause,[],[f427])).
% 1.68/0.63  fof(f1337,plain,(
% 1.68/0.63    spl13_34 | ~spl13_20),
% 1.68/0.63    inference(avatar_split_clause,[],[f1323,f202,f431])).
% 1.68/0.63  fof(f1323,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK1)) | ~spl13_20),
% 1.68/0.63    inference(resolution,[],[f204,f88])).
% 1.68/0.63  fof(f204,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))) | ~spl13_20),
% 1.68/0.63    inference(avatar_component_clause,[],[f202])).
% 1.68/0.63  fof(f1336,plain,(
% 1.68/0.63    spl13_33 | ~spl13_20),
% 1.68/0.63    inference(avatar_split_clause,[],[f1322,f202,f427])).
% 1.68/0.63  fof(f1322,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,sK0)) | ~spl13_20),
% 1.68/0.63    inference(resolution,[],[f204,f89])).
% 1.68/0.63  fof(f1279,plain,(
% 1.68/0.63    ~spl13_18),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f1276])).
% 1.68/0.63  fof(f1276,plain,(
% 1.68/0.63    $false | ~spl13_18),
% 1.68/0.63    inference(resolution,[],[f196,f78])).
% 1.68/0.63  fof(f78,plain,(
% 1.68/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f45,f46])).
% 1.68/0.63  fof(f45,plain,(
% 1.68/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f4])).
% 1.68/0.63  fof(f4,axiom,(
% 1.68/0.63    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.68/0.63  fof(f196,plain,(
% 1.68/0.63    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X2,X3))) ) | ~spl13_18),
% 1.68/0.63    inference(avatar_component_clause,[],[f195])).
% 1.68/0.63  fof(f1263,plain,(
% 1.68/0.63    ~spl13_17),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f1258])).
% 1.68/0.63  fof(f1258,plain,(
% 1.68/0.63    $false | ~spl13_17),
% 1.68/0.63    inference(resolution,[],[f193,f86])).
% 1.68/0.63  fof(f86,plain,(
% 1.68/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.68/0.63    inference(equality_resolution,[],[f47])).
% 1.68/0.63  fof(f47,plain,(
% 1.68/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.68/0.63    inference(cnf_transformation,[],[f21])).
% 1.68/0.63  fof(f21,plain,(
% 1.68/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.68/0.63    inference(flattening,[],[f20])).
% 1.68/0.63  fof(f20,plain,(
% 1.68/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.68/0.63    inference(nnf_transformation,[],[f3])).
% 1.68/0.63  fof(f3,axiom,(
% 1.68/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.68/0.63  fof(f193,plain,(
% 1.68/0.63    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_zfmisc_1(X4,X5))) ) | ~spl13_17),
% 1.68/0.63    inference(avatar_component_clause,[],[f192])).
% 1.68/0.63  fof(f1255,plain,(
% 1.68/0.63    spl13_7 | spl13_8 | spl13_10 | spl13_1 | spl13_9),
% 1.68/0.63    inference(avatar_split_clause,[],[f1038,f149,f110,f153,f146,f143])).
% 1.68/0.63  fof(f143,plain,(
% 1.68/0.63    spl13_7 <=> ! [X5,X4] : ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k2_zfmisc_1(X4,X5))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 1.68/0.63  fof(f146,plain,(
% 1.68/0.63    spl13_8 <=> ! [X3,X2] : ~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X2,X3))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 1.68/0.63  fof(f153,plain,(
% 1.68/0.63    spl13_10 <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 1.68/0.63  fof(f110,plain,(
% 1.68/0.63    spl13_1 <=> sQ12_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.68/0.63  fof(f149,plain,(
% 1.68/0.63    spl13_9 <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 1.68/0.63  fof(f1038,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (sQ12_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) | r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) | ~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k2_zfmisc_1(X2,X3))) ) | spl13_9),
% 1.68/0.63    inference(resolution,[],[f150,f107])).
% 1.68/0.63  fof(f150,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)) | spl13_9),
% 1.68/0.63    inference(avatar_component_clause,[],[f149])).
% 1.68/0.63  fof(f1251,plain,(
% 1.68/0.63    spl13_42 | ~spl13_9),
% 1.68/0.63    inference(avatar_split_clause,[],[f348,f149,f1010])).
% 1.68/0.63  fof(f1010,plain,(
% 1.68/0.63    spl13_42 <=> r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).
% 1.68/0.63  fof(f348,plain,(
% 1.68/0.63    r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2) | ~spl13_9),
% 1.68/0.63    inference(resolution,[],[f151,f73])).
% 1.68/0.63  fof(f73,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f40])).
% 1.68/0.63  fof(f151,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)) | ~spl13_9),
% 1.68/0.63    inference(avatar_component_clause,[],[f149])).
% 1.68/0.63  fof(f1250,plain,(
% 1.68/0.63    ~spl13_44 | ~spl13_42 | spl13_32),
% 1.68/0.63    inference(avatar_split_clause,[],[f1018,f413,f1010,f1166])).
% 1.68/0.63  fof(f1166,plain,(
% 1.68/0.63    spl13_44 <=> r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).
% 1.68/0.63  fof(f413,plain,(
% 1.68/0.63    spl13_32 <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).
% 1.68/0.63  fof(f1018,plain,(
% 1.68/0.63    ~r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2) | ~r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1) | spl13_32),
% 1.68/0.63    inference(resolution,[],[f415,f91])).
% 1.68/0.63  fof(f415,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2)) | spl13_32),
% 1.68/0.63    inference(avatar_component_clause,[],[f413])).
% 1.68/0.63  fof(f1247,plain,(
% 1.68/0.63    ~spl13_31 | ~spl13_32 | spl13_10),
% 1.68/0.63    inference(avatar_split_clause,[],[f400,f153,f413,f409])).
% 1.68/0.63  fof(f409,plain,(
% 1.68/0.63    spl13_31 <=> r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_31])])).
% 1.68/0.63  fof(f400,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2)) | spl13_10),
% 1.68/0.63    inference(resolution,[],[f154,f87])).
% 1.68/0.63  fof(f154,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) | spl13_10),
% 1.68/0.63    inference(avatar_component_clause,[],[f153])).
% 1.68/0.63  fof(f1245,plain,(
% 1.68/0.63    spl13_44 | ~spl13_9),
% 1.68/0.63    inference(avatar_split_clause,[],[f553,f149,f1166])).
% 1.68/0.63  fof(f553,plain,(
% 1.68/0.63    r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1) | ~spl13_9),
% 1.68/0.63    inference(resolution,[],[f347,f88])).
% 1.68/0.63  fof(f347,plain,(
% 1.68/0.63    r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl13_9),
% 1.68/0.63    inference(resolution,[],[f151,f72])).
% 1.68/0.63  fof(f1243,plain,(
% 1.68/0.63    spl13_44 | ~spl13_32),
% 1.68/0.63    inference(avatar_split_clause,[],[f1226,f413,f1166])).
% 1.68/0.63  fof(f1226,plain,(
% 1.68/0.63    r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1) | ~spl13_32),
% 1.68/0.63    inference(resolution,[],[f414,f69])).
% 1.68/0.63  fof(f69,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f38])).
% 1.68/0.63  fof(f414,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2)) | ~spl13_32),
% 1.68/0.63    inference(avatar_component_clause,[],[f413])).
% 1.68/0.63  fof(f1169,plain,(
% 1.68/0.63    ~spl13_41 | ~spl13_44 | spl13_43),
% 1.68/0.63    inference(avatar_split_clause,[],[f1157,f1085,f1166,f1006])).
% 1.68/0.63  fof(f1006,plain,(
% 1.68/0.63    spl13_41 <=> r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).
% 1.68/0.63  fof(f1085,plain,(
% 1.68/0.63    spl13_43 <=> r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_43])])).
% 1.68/0.63  fof(f1157,plain,(
% 1.68/0.63    ~r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK1) | ~r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0) | spl13_43),
% 1.68/0.63    inference(resolution,[],[f1087,f87])).
% 1.68/0.63  fof(f1087,plain,(
% 1.68/0.63    ~r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl13_43),
% 1.68/0.63    inference(avatar_component_clause,[],[f1085])).
% 1.68/0.63  fof(f1090,plain,(
% 1.68/0.63    ~spl13_43 | ~spl13_42 | spl13_9),
% 1.68/0.63    inference(avatar_split_clause,[],[f1035,f149,f1010,f1085])).
% 1.68/0.63  fof(f1035,plain,(
% 1.68/0.63    ~r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2) | ~r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl13_9),
% 1.68/0.63    inference(resolution,[],[f150,f74])).
% 1.68/0.63  fof(f74,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f40])).
% 1.68/0.63  fof(f1083,plain,(
% 1.68/0.63    spl13_42 | ~spl13_31),
% 1.68/0.63    inference(avatar_split_clause,[],[f1065,f409,f1010])).
% 1.68/0.63  fof(f1065,plain,(
% 1.68/0.63    r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2) | ~spl13_31),
% 1.68/0.63    inference(resolution,[],[f410,f70])).
% 1.68/0.63  fof(f410,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2)) | ~spl13_31),
% 1.68/0.63    inference(avatar_component_clause,[],[f409])).
% 1.68/0.63  fof(f1082,plain,(
% 1.68/0.63    spl13_41 | ~spl13_31),
% 1.68/0.63    inference(avatar_split_clause,[],[f1064,f409,f1006])).
% 1.68/0.63  fof(f1064,plain,(
% 1.68/0.63    r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0) | ~spl13_31),
% 1.68/0.63    inference(resolution,[],[f410,f69])).
% 1.68/0.63  fof(f1061,plain,(
% 1.68/0.63    spl13_32 | ~spl13_10),
% 1.68/0.63    inference(avatar_split_clause,[],[f1047,f153,f413])).
% 1.68/0.63  fof(f1047,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK1,sK2)) | ~spl13_10),
% 1.68/0.63    inference(resolution,[],[f155,f88])).
% 1.68/0.63  fof(f155,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) | ~spl13_10),
% 1.68/0.63    inference(avatar_component_clause,[],[f153])).
% 1.68/0.63  fof(f1060,plain,(
% 1.68/0.63    spl13_31 | ~spl13_10),
% 1.68/0.63    inference(avatar_split_clause,[],[f1046,f153,f409])).
% 1.68/0.63  fof(f1046,plain,(
% 1.68/0.63    r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2)) | ~spl13_10),
% 1.68/0.63    inference(resolution,[],[f155,f89])).
% 1.68/0.63  fof(f1034,plain,(
% 1.68/0.63    ~spl13_9 | spl13_41),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f1026])).
% 1.68/0.63  fof(f1026,plain,(
% 1.68/0.63    $false | (~spl13_9 | spl13_41)),
% 1.68/0.63    inference(resolution,[],[f1008,f552])).
% 1.68/0.63  fof(f552,plain,(
% 1.68/0.63    r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0) | ~spl13_9),
% 1.68/0.63    inference(resolution,[],[f347,f89])).
% 1.68/0.63  fof(f1008,plain,(
% 1.68/0.63    ~r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0) | spl13_41),
% 1.68/0.63    inference(avatar_component_clause,[],[f1006])).
% 1.68/0.63  fof(f1015,plain,(
% 1.68/0.63    ~spl13_41 | ~spl13_42 | spl13_31),
% 1.68/0.63    inference(avatar_split_clause,[],[f997,f409,f1010,f1006])).
% 1.68/0.63  fof(f997,plain,(
% 1.68/0.63    ~r2_hidden(sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK2) | ~r2_hidden(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK0) | spl13_31),
% 1.68/0.63    inference(resolution,[],[f411,f91])).
% 1.68/0.63  fof(f411,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(sK0,sK2)) | spl13_31),
% 1.68/0.63    inference(avatar_component_clause,[],[f409])).
% 1.68/0.63  fof(f581,plain,(
% 1.68/0.63    ~spl13_35 | ~spl13_36 | spl13_30),
% 1.68/0.63    inference(avatar_split_clause,[],[f565,f382,f578,f574])).
% 1.68/0.63  fof(f565,plain,(
% 1.68/0.63    ~r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK1) | ~r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK0) | spl13_30),
% 1.68/0.63    inference(resolution,[],[f384,f87])).
% 1.68/0.63  fof(f384,plain,(
% 1.68/0.63    ~r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl13_30),
% 1.68/0.63    inference(avatar_component_clause,[],[f382])).
% 1.68/0.63  fof(f387,plain,(
% 1.68/0.63    ~spl13_29 | ~spl13_30 | spl13_19),
% 1.68/0.63    inference(avatar_split_clause,[],[f368,f198,f382,f378])).
% 1.68/0.63  fof(f368,plain,(
% 1.68/0.63    ~r2_hidden(sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~r2_hidden(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK2) | spl13_19),
% 1.68/0.63    inference(resolution,[],[f199,f91])).
% 1.68/0.63  fof(f199,plain,(
% 1.68/0.63    ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl13_19),
% 1.68/0.63    inference(avatar_component_clause,[],[f198])).
% 1.68/0.63  fof(f235,plain,(
% 1.68/0.63    ~spl13_8),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f232])).
% 1.68/0.63  fof(f232,plain,(
% 1.68/0.63    $false | ~spl13_8),
% 1.68/0.63    inference(resolution,[],[f147,f78])).
% 1.68/0.63  fof(f147,plain,(
% 1.68/0.63    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X2,X3))) ) | ~spl13_8),
% 1.68/0.63    inference(avatar_component_clause,[],[f146])).
% 1.68/0.63  fof(f229,plain,(
% 1.68/0.63    ~spl13_7),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f224])).
% 1.68/0.63  fof(f224,plain,(
% 1.68/0.63    $false | ~spl13_7),
% 1.68/0.63    inference(resolution,[],[f144,f86])).
% 1.68/0.63  fof(f144,plain,(
% 1.68/0.63    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k2_zfmisc_1(X4,X5))) ) | ~spl13_7),
% 1.68/0.63    inference(avatar_component_clause,[],[f143])).
% 1.68/0.63  fof(f206,plain,(
% 1.68/0.63    spl13_17 | spl13_18 | ~spl13_19 | ~spl13_20 | spl13_2),
% 1.68/0.63    inference(avatar_split_clause,[],[f171,f114,f202,f198,f195,f192])).
% 1.68/0.63  fof(f171,plain,(
% 1.68/0.63    ( ! [X6,X8,X7,X9] : (~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))) | ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),sK11(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))),k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X6,X7)) | ~r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_zfmisc_1(X8,X9))) ) | spl13_2),
% 1.68/0.63    inference(resolution,[],[f116,f106])).
% 1.68/0.63  fof(f106,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (sQ12_eqProxy(X0,X3) | ~r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3) | ~r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0) | ~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 1.68/0.63    inference(equality_proxy_replacement,[],[f76,f95])).
% 1.68/0.63  fof(f76,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | ~r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X3) | ~r2_hidden(k4_tarski(sK10(X0,X3),sK11(X0,X3)),X0) | ~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f43])).
% 1.68/0.63  fof(f116,plain,(
% 1.68/0.63    ~sQ12_eqProxy(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))) | spl13_2),
% 1.68/0.63    inference(avatar_component_clause,[],[f114])).
% 1.68/0.63  fof(f157,plain,(
% 1.68/0.63    spl13_7 | spl13_8 | ~spl13_9 | ~spl13_10 | spl13_1),
% 1.68/0.63    inference(avatar_split_clause,[],[f122,f110,f153,f149,f146,f143])).
% 1.68/0.63  fof(f122,plain,(
% 1.68/0.63    ( ! [X6,X8,X7,X9] : (~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) | ~r2_hidden(k4_tarski(sK10(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),sK11(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)) | ~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X6,X7)) | ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k2_zfmisc_1(X8,X9))) ) | spl13_1),
% 1.68/0.63    inference(resolution,[],[f112,f106])).
% 1.68/0.63  fof(f112,plain,(
% 1.68/0.63    ~sQ12_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))) | spl13_1),
% 1.68/0.63    inference(avatar_component_clause,[],[f110])).
% 1.68/0.63  fof(f117,plain,(
% 1.68/0.63    ~spl13_1 | ~spl13_2),
% 1.68/0.63    inference(avatar_split_clause,[],[f96,f114,f110])).
% 1.68/0.63  fof(f96,plain,(
% 1.68/0.63    ~sQ12_eqProxy(k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))) | ~sQ12_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))),
% 1.68/0.63    inference(equality_proxy_replacement,[],[f77,f95,f95])).
% 1.68/0.63  fof(f77,plain,(
% 1.68/0.63    k2_zfmisc_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))) | k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),
% 1.68/0.63    inference(definition_unfolding,[],[f44,f46,f46,f46,f46])).
% 1.68/0.63  fof(f44,plain,(
% 1.68/0.63    k2_zfmisc_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),
% 1.68/0.63    inference(cnf_transformation,[],[f19])).
% 1.68/0.63  fof(f19,plain,(
% 1.68/0.63    k2_zfmisc_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),
% 1.68/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).
% 1.68/0.63  fof(f18,plain,(
% 1.68/0.63    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | k2_zfmisc_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) => (k2_zfmisc_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f13,plain,(
% 1.68/0.63    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | k2_zfmisc_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.68/0.63    inference(ennf_transformation,[],[f12])).
% 1.68/0.63  fof(f12,negated_conjecture,(
% 1.68/0.63    ~! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.68/0.63    inference(negated_conjecture,[],[f11])).
% 1.68/0.63  fof(f11,conjecture,(
% 1.68/0.63    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 1.68/0.63  % SZS output end Proof for theBenchmark
% 1.68/0.63  % (8931)------------------------------
% 1.68/0.63  % (8931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.63  % (8931)Termination reason: Refutation
% 1.68/0.63  
% 1.68/0.63  % (8931)Memory used [KB]: 7291
% 1.68/0.63  % (8931)Time elapsed: 0.209 s
% 1.68/0.63  % (8931)------------------------------
% 1.68/0.63  % (8931)------------------------------
% 2.01/0.63  % (8912)Success in time 0.271 s
%------------------------------------------------------------------------------
