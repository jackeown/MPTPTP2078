%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:51 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 342 expanded)
%              Number of leaves         :   19 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  467 (2221 expanded)
%              Number of equality atoms :  108 ( 472 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f313,f339,f342,f406,f443])).

fof(f443,plain,(
    spl13_2 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl13_2 ),
    inference(subsumption_resolution,[],[f441,f86])).

fof(f86,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f38,f85])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
            | ~ r2_hidden(sK12(X0,X1,X2),X0)
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK12(X0,X1,X2),X1)
              & r2_hidden(sK12(X0,X1,X2),X0) )
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
          | ~ r2_hidden(sK12(X0,X1,X2),X0)
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK12(X0,X1,X2),X1)
            & r2_hidden(sK12(X0,X1,X2),X0) )
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f38,plain,(
    r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X5,X6] :
        ( ~ r2_hidden(X6,k3_xboole_0(sK2,sK4))
        | ~ r2_hidden(X5,k3_xboole_0(sK1,sK3))
        | k4_tarski(X5,X6) != sK0 )
    & r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6] :
            ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
            | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
            | k4_tarski(X5,X6) != X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) )
   => ( ! [X6,X5] :
          ( ~ r2_hidden(X6,k3_xboole_0(sK2,sK4))
          | ~ r2_hidden(X5,k3_xboole_0(sK1,sK3))
          | k4_tarski(X5,X6) != sK0 )
      & r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6] :
          ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
          | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
          | k4_tarski(X5,X6) != X0 )
      & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6] :
              ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X5,k3_xboole_0(X1,X3))
                & k4_tarski(X5,X6) = X0 )
          & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(f441,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | spl13_2 ),
    inference(resolution,[],[f440,f82])).

fof(f82,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
              & r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
                & r2_hidden(sK11(X0,X1,X8),X1)
                & r2_hidden(sK10(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f26,f29,f28,f27])).

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
              ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
        & r2_hidden(sK11(X0,X1,X8),X1)
        & r2_hidden(sK10(X0,X1,X8),X0) ) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f440,plain,
    ( ~ r2_hidden(sK10(sK1,sK2,sK0),sK1)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f439,f385])).

fof(f385,plain,(
    r2_hidden(sK10(sK1,sK2,sK0),sK3) ),
    inference(subsumption_resolution,[],[f383,f72])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f383,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK10(sK1,sK2,sK0),sK3) ),
    inference(superposition,[],[f192,f91])).

fof(f91,plain,(
    sK0 = k4_tarski(sK10(sK1,sK2,sK0),sK11(sK1,sK2,sK0)) ),
    inference(resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f192,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k1_tarski(sK0))
      | r2_hidden(X6,sK3) ) ),
    inference(resolution,[],[f138,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f138,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_zfmisc_1(sK3,sK4))
      | ~ r2_hidden(X2,k1_tarski(sK0)) ) ),
    inference(global_subsumption,[],[f106,f131,f136])).

fof(f136,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,k2_zfmisc_1(sK3,sK4))
      | ~ r2_hidden(X2,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f75,f98])).

fof(f98,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f87,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f38,f84])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f131,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))
      | ~ r2_hidden(X1,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f84,f89])).

fof(f89,plain,(
    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    inference(resolution,[],[f38,f74])).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k1_tarski(X2) = k3_xboole_0(k2_tarski(X2,X2),X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ) ),
    inference(superposition,[],[f76,f90])).

fof(f90,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    inference(resolution,[],[f38,f45])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f439,plain,
    ( ~ r2_hidden(sK10(sK1,sK2,sK0),sK3)
    | ~ r2_hidden(sK10(sK1,sK2,sK0),sK1)
    | spl13_2 ),
    inference(resolution,[],[f312,f83])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f312,plain,
    ( ~ r2_hidden(sK10(sK1,sK2,sK0),k3_xboole_0(sK1,sK3))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl13_2
  <=> r2_hidden(sK10(sK1,sK2,sK0),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f406,plain,(
    spl13_4 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | spl13_4 ),
    inference(subsumption_resolution,[],[f404,f338])).

fof(f338,plain,
    ( ~ r2_hidden(sK11(sK1,sK2,sK0),sK4)
    | spl13_4 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl13_4
  <=> r2_hidden(sK11(sK1,sK2,sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f404,plain,(
    r2_hidden(sK11(sK1,sK2,sK0),sK4) ),
    inference(subsumption_resolution,[],[f402,f72])).

fof(f402,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK11(sK1,sK2,sK0),sK4) ),
    inference(superposition,[],[f193,f91])).

fof(f193,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k1_tarski(sK0))
      | r2_hidden(X9,sK4) ) ),
    inference(resolution,[],[f138,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f342,plain,(
    spl13_3 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | spl13_3 ),
    inference(subsumption_resolution,[],[f340,f86])).

fof(f340,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | spl13_3 ),
    inference(resolution,[],[f334,f81])).

fof(f81,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f334,plain,
    ( ~ r2_hidden(sK11(sK1,sK2,sK0),sK2)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl13_3
  <=> r2_hidden(sK11(sK1,sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f339,plain,
    ( ~ spl13_3
    | ~ spl13_4
    | spl13_1 ),
    inference(avatar_split_clause,[],[f330,f306,f336,f332])).

fof(f306,plain,
    ( spl13_1
  <=> r2_hidden(sK11(sK1,sK2,sK0),k3_xboole_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f330,plain,
    ( ~ r2_hidden(sK11(sK1,sK2,sK0),sK4)
    | ~ r2_hidden(sK11(sK1,sK2,sK0),sK2)
    | spl13_1 ),
    inference(resolution,[],[f308,f83])).

fof(f308,plain,
    ( ~ r2_hidden(sK11(sK1,sK2,sK0),k3_xboole_0(sK2,sK4))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f306])).

fof(f313,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f304,f310,f306])).

fof(f304,plain,
    ( ~ r2_hidden(sK10(sK1,sK2,sK0),k3_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK11(sK1,sK2,sK0),k3_xboole_0(sK2,sK4)) ),
    inference(trivial_inequality_removal,[],[f298])).

fof(f298,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK10(sK1,sK2,sK0),k3_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK11(sK1,sK2,sK0),k3_xboole_0(sK2,sK4)) ),
    inference(superposition,[],[f39,f91])).

fof(f39,plain,(
    ! [X6,X5] :
      ( k4_tarski(X5,X6) != sK0
      | ~ r2_hidden(X5,k3_xboole_0(sK1,sK3))
      | ~ r2_hidden(X6,k3_xboole_0(sK2,sK4)) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:27:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.49/0.57  % (19126)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.49/0.58  % (19118)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.49/0.58  % (19123)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.49/0.58  % (19136)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.49/0.58  % (19134)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.49/0.58  % (19128)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.49/0.58  % (19129)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.49/0.59  % (19120)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.49/0.59  % (19121)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.49/0.59  % (19133)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.49/0.59  % (19121)Refutation not found, incomplete strategy% (19121)------------------------------
% 1.49/0.59  % (19121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (19121)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (19121)Memory used [KB]: 10618
% 1.49/0.59  % (19121)Time elapsed: 0.138 s
% 1.49/0.59  % (19121)------------------------------
% 1.49/0.59  % (19121)------------------------------
% 1.49/0.59  % (19125)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.49/0.59  % (19139)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.49/0.59  % (19131)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.49/0.59  % (19137)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.49/0.59  % (19119)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.49/0.60  % (19117)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.49/0.60  % (19127)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.49/0.61  % (19132)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.49/0.61  % (19138)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.49/0.61  % (19135)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.49/0.61  % (19116)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.61  % (19115)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.49/0.61  % (19140)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.49/0.62  % (19124)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.49/0.62  % (19122)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.49/0.62  % (19130)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.49/0.64  % (19116)Refutation found. Thanks to Tanya!
% 1.49/0.64  % SZS status Theorem for theBenchmark
% 2.18/0.66  % SZS output start Proof for theBenchmark
% 2.18/0.66  fof(f444,plain,(
% 2.18/0.66    $false),
% 2.18/0.66    inference(avatar_sat_refutation,[],[f313,f339,f342,f406,f443])).
% 2.18/0.66  fof(f443,plain,(
% 2.18/0.66    spl13_2),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f442])).
% 2.18/0.66  fof(f442,plain,(
% 2.18/0.66    $false | spl13_2),
% 2.18/0.66    inference(subsumption_resolution,[],[f441,f86])).
% 2.18/0.66  fof(f86,plain,(
% 2.18/0.66    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 2.18/0.66    inference(resolution,[],[f38,f85])).
% 2.18/0.66  fof(f85,plain,(
% 2.18/0.66    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.18/0.66    inference(equality_resolution,[],[f62])).
% 2.18/0.66  fof(f62,plain,(
% 2.18/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f35])).
% 2.18/0.66  fof(f35,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK12(X0,X1,X2),X1) | ~r2_hidden(sK12(X0,X1,X2),X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & ((r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK12(X0,X1,X2),X0)) | r2_hidden(sK12(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f33,f34])).
% 2.18/0.66  fof(f34,plain,(
% 2.18/0.66    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK12(X0,X1,X2),X1) | ~r2_hidden(sK12(X0,X1,X2),X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & ((r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK12(X0,X1,X2),X0)) | r2_hidden(sK12(X0,X1,X2),X2))))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f33,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.18/0.66    inference(rectify,[],[f32])).
% 2.18/0.66  fof(f32,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.18/0.66    inference(flattening,[],[f31])).
% 2.18/0.66  fof(f31,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.18/0.66    inference(nnf_transformation,[],[f1])).
% 2.18/0.66  fof(f1,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.18/0.66  fof(f38,plain,(
% 2.18/0.66    r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 2.18/0.66    inference(cnf_transformation,[],[f14])).
% 2.18/0.66  fof(f14,plain,(
% 2.18/0.66    ! [X5,X6] : (~r2_hidden(X6,k3_xboole_0(sK2,sK4)) | ~r2_hidden(X5,k3_xboole_0(sK1,sK3)) | k4_tarski(X5,X6) != sK0) & r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f13])).
% 2.18/0.66  fof(f13,plain,(
% 2.18/0.66    ? [X0,X1,X2,X3,X4] : (! [X5,X6] : (~r2_hidden(X6,k3_xboole_0(X2,X4)) | ~r2_hidden(X5,k3_xboole_0(X1,X3)) | k4_tarski(X5,X6) != X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) => (! [X6,X5] : (~r2_hidden(X6,k3_xboole_0(sK2,sK4)) | ~r2_hidden(X5,k3_xboole_0(sK1,sK3)) | k4_tarski(X5,X6) != sK0) & r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f10,plain,(
% 2.18/0.66    ? [X0,X1,X2,X3,X4] : (! [X5,X6] : (~r2_hidden(X6,k3_xboole_0(X2,X4)) | ~r2_hidden(X5,k3_xboole_0(X1,X3)) | k4_tarski(X5,X6) != X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 2.18/0.66    inference(ennf_transformation,[],[f9])).
% 2.18/0.66  fof(f9,negated_conjecture,(
% 2.18/0.66    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 2.18/0.66    inference(negated_conjecture,[],[f8])).
% 2.18/0.66  fof(f8,conjecture,(
% 2.18/0.66    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).
% 2.18/0.66  fof(f441,plain,(
% 2.18/0.66    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | spl13_2),
% 2.18/0.66    inference(resolution,[],[f440,f82])).
% 2.18/0.66  fof(f82,plain,(
% 2.18/0.66    ( ! [X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.18/0.66    inference(equality_resolution,[],[f54])).
% 2.18/0.66  fof(f54,plain,(
% 2.18/0.66    ( ! [X2,X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f30])).
% 2.18/0.66  fof(f30,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f26,f29,f28,f27])).
% 2.18/0.66  fof(f27,plain,(
% 2.18/0.66    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f28,plain,(
% 2.18/0.66    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f29,plain,(
% 2.18/0.66    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f26,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.18/0.66    inference(rectify,[],[f25])).
% 2.18/0.66  fof(f25,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.18/0.66    inference(nnf_transformation,[],[f4])).
% 2.18/0.66  fof(f4,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.18/0.66  fof(f440,plain,(
% 2.18/0.66    ~r2_hidden(sK10(sK1,sK2,sK0),sK1) | spl13_2),
% 2.18/0.66    inference(subsumption_resolution,[],[f439,f385])).
% 2.18/0.66  fof(f385,plain,(
% 2.18/0.66    r2_hidden(sK10(sK1,sK2,sK0),sK3)),
% 2.18/0.66    inference(subsumption_resolution,[],[f383,f72])).
% 2.18/0.66  fof(f72,plain,(
% 2.18/0.66    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.18/0.66    inference(equality_resolution,[],[f71])).
% 2.18/0.66  fof(f71,plain,(
% 2.18/0.66    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.18/0.66    inference(equality_resolution,[],[f41])).
% 2.18/0.66  fof(f41,plain,(
% 2.18/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.18/0.66    inference(cnf_transformation,[],[f18])).
% 2.18/0.66  fof(f18,plain,(
% 2.18/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f17])).
% 2.18/0.66  fof(f17,plain,(
% 2.18/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f16,plain,(
% 2.18/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.18/0.66    inference(rectify,[],[f15])).
% 2.18/0.66  fof(f15,plain,(
% 2.18/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.18/0.66    inference(nnf_transformation,[],[f3])).
% 2.18/0.66  fof(f3,axiom,(
% 2.18/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.18/0.66  fof(f383,plain,(
% 2.18/0.66    ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK10(sK1,sK2,sK0),sK3)),
% 2.18/0.66    inference(superposition,[],[f192,f91])).
% 2.18/0.66  fof(f91,plain,(
% 2.18/0.66    sK0 = k4_tarski(sK10(sK1,sK2,sK0),sK11(sK1,sK2,sK0))),
% 2.18/0.66    inference(resolution,[],[f86,f80])).
% 2.18/0.66  fof(f80,plain,(
% 2.18/0.66    ( ! [X0,X8,X1] : (~r2_hidden(X8,k2_zfmisc_1(X0,X1)) | k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8) )),
% 2.18/0.66    inference(equality_resolution,[],[f56])).
% 2.18/0.66  fof(f56,plain,(
% 2.18/0.66    ( ! [X2,X0,X8,X1] : (k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f30])).
% 2.18/0.66  fof(f192,plain,(
% 2.18/0.66    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),k1_tarski(sK0)) | r2_hidden(X6,sK3)) )),
% 2.18/0.66    inference(resolution,[],[f138,f68])).
% 2.18/0.66  fof(f68,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f37])).
% 2.18/0.66  fof(f37,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.18/0.66    inference(flattening,[],[f36])).
% 2.18/0.66  fof(f36,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.18/0.66    inference(nnf_transformation,[],[f5])).
% 2.18/0.66  fof(f5,axiom,(
% 2.18/0.66    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.18/0.66  fof(f138,plain,(
% 2.18/0.66    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(sK3,sK4)) | ~r2_hidden(X2,k1_tarski(sK0))) )),
% 2.18/0.66    inference(global_subsumption,[],[f106,f131,f136])).
% 2.18/0.66  fof(f136,plain,(
% 2.18/0.66    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,k2_zfmisc_1(sK3,sK4)) | ~r2_hidden(X2,k1_tarski(sK0))) )),
% 2.18/0.66    inference(superposition,[],[f75,f98])).
% 2.18/0.66  fof(f98,plain,(
% 2.18/0.66    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK3,sK4))),
% 2.18/0.66    inference(resolution,[],[f87,f45])).
% 2.18/0.66  fof(f45,plain,(
% 2.18/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) )),
% 2.18/0.66    inference(cnf_transformation,[],[f19])).
% 2.18/0.66  fof(f19,plain,(
% 2.18/0.66    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 2.18/0.66    inference(nnf_transformation,[],[f7])).
% 2.18/0.66  fof(f7,axiom,(
% 2.18/0.66    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 2.18/0.66  fof(f87,plain,(
% 2.18/0.66    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))),
% 2.18/0.66    inference(resolution,[],[f38,f84])).
% 2.18/0.66  fof(f84,plain,(
% 2.18/0.66    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 2.18/0.66    inference(equality_resolution,[],[f63])).
% 2.18/0.66  fof(f63,plain,(
% 2.18/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f35])).
% 2.18/0.66  fof(f75,plain,(
% 2.18/0.66    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.18/0.66    inference(equality_resolution,[],[f50])).
% 2.18/0.66  fof(f50,plain,(
% 2.18/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f24])).
% 2.18/0.66  fof(f24,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).
% 2.18/0.66  fof(f23,plain,(
% 2.18/0.66    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f22,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.18/0.66    inference(rectify,[],[f21])).
% 2.18/0.66  fof(f21,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.18/0.66    inference(flattening,[],[f20])).
% 2.18/0.66  fof(f20,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.18/0.66    inference(nnf_transformation,[],[f2])).
% 2.18/0.66  fof(f2,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.18/0.66  fof(f131,plain,(
% 2.18/0.66    ( ! [X1] : (r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) | ~r2_hidden(X1,k1_tarski(sK0))) )),
% 2.18/0.66    inference(superposition,[],[f84,f89])).
% 2.18/0.66  fof(f89,plain,(
% 2.18/0.66    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 2.18/0.66    inference(resolution,[],[f38,f74])).
% 2.18/0.66  fof(f74,plain,(
% 2.18/0.66    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k1_tarski(X2) = k3_xboole_0(k2_tarski(X2,X2),X1)) )),
% 2.18/0.66    inference(equality_resolution,[],[f47])).
% 2.18/0.66  fof(f47,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f12])).
% 2.18/0.66  fof(f12,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.18/0.66    inference(flattening,[],[f11])).
% 2.18/0.66  fof(f11,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 2.18/0.66    inference(ennf_transformation,[],[f6])).
% 2.18/0.66  fof(f6,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 2.18/0.66  fof(f106,plain,(
% 2.18/0.66    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))) )),
% 2.18/0.66    inference(superposition,[],[f76,f90])).
% 2.18/0.66  fof(f90,plain,(
% 2.18/0.66    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 2.18/0.66    inference(resolution,[],[f38,f45])).
% 2.18/0.66  fof(f76,plain,(
% 2.18/0.66    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.18/0.66    inference(equality_resolution,[],[f49])).
% 2.18/0.66  fof(f49,plain,(
% 2.18/0.66    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f24])).
% 2.18/0.66  fof(f439,plain,(
% 2.18/0.66    ~r2_hidden(sK10(sK1,sK2,sK0),sK3) | ~r2_hidden(sK10(sK1,sK2,sK0),sK1) | spl13_2),
% 2.18/0.66    inference(resolution,[],[f312,f83])).
% 2.18/0.66  fof(f83,plain,(
% 2.18/0.66    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.18/0.66    inference(equality_resolution,[],[f64])).
% 2.18/0.66  fof(f64,plain,(
% 2.18/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f35])).
% 2.18/0.66  fof(f312,plain,(
% 2.18/0.66    ~r2_hidden(sK10(sK1,sK2,sK0),k3_xboole_0(sK1,sK3)) | spl13_2),
% 2.18/0.66    inference(avatar_component_clause,[],[f310])).
% 2.18/0.66  fof(f310,plain,(
% 2.18/0.66    spl13_2 <=> r2_hidden(sK10(sK1,sK2,sK0),k3_xboole_0(sK1,sK3))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 2.18/0.66  fof(f406,plain,(
% 2.18/0.66    spl13_4),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f405])).
% 2.18/0.66  fof(f405,plain,(
% 2.18/0.66    $false | spl13_4),
% 2.18/0.66    inference(subsumption_resolution,[],[f404,f338])).
% 2.18/0.66  fof(f338,plain,(
% 2.18/0.66    ~r2_hidden(sK11(sK1,sK2,sK0),sK4) | spl13_4),
% 2.18/0.66    inference(avatar_component_clause,[],[f336])).
% 2.18/0.66  fof(f336,plain,(
% 2.18/0.66    spl13_4 <=> r2_hidden(sK11(sK1,sK2,sK0),sK4)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 2.18/0.66  fof(f404,plain,(
% 2.18/0.66    r2_hidden(sK11(sK1,sK2,sK0),sK4)),
% 2.18/0.66    inference(subsumption_resolution,[],[f402,f72])).
% 2.18/0.66  fof(f402,plain,(
% 2.18/0.66    ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK11(sK1,sK2,sK0),sK4)),
% 2.18/0.66    inference(superposition,[],[f193,f91])).
% 2.18/0.66  fof(f193,plain,(
% 2.18/0.66    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k1_tarski(sK0)) | r2_hidden(X9,sK4)) )),
% 2.18/0.66    inference(resolution,[],[f138,f69])).
% 2.18/0.66  fof(f69,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f37])).
% 2.18/0.66  fof(f342,plain,(
% 2.18/0.66    spl13_3),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f341])).
% 2.18/0.66  fof(f341,plain,(
% 2.18/0.66    $false | spl13_3),
% 2.18/0.66    inference(subsumption_resolution,[],[f340,f86])).
% 2.18/0.66  fof(f340,plain,(
% 2.18/0.66    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | spl13_3),
% 2.18/0.66    inference(resolution,[],[f334,f81])).
% 2.18/0.66  fof(f81,plain,(
% 2.18/0.66    ( ! [X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.18/0.66    inference(equality_resolution,[],[f55])).
% 2.18/0.66  fof(f55,plain,(
% 2.18/0.66    ( ! [X2,X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f30])).
% 2.18/0.66  fof(f334,plain,(
% 2.18/0.66    ~r2_hidden(sK11(sK1,sK2,sK0),sK2) | spl13_3),
% 2.18/0.66    inference(avatar_component_clause,[],[f332])).
% 2.18/0.66  fof(f332,plain,(
% 2.18/0.66    spl13_3 <=> r2_hidden(sK11(sK1,sK2,sK0),sK2)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 2.18/0.66  fof(f339,plain,(
% 2.18/0.66    ~spl13_3 | ~spl13_4 | spl13_1),
% 2.18/0.66    inference(avatar_split_clause,[],[f330,f306,f336,f332])).
% 2.18/0.66  fof(f306,plain,(
% 2.18/0.66    spl13_1 <=> r2_hidden(sK11(sK1,sK2,sK0),k3_xboole_0(sK2,sK4))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 2.18/0.66  fof(f330,plain,(
% 2.18/0.66    ~r2_hidden(sK11(sK1,sK2,sK0),sK4) | ~r2_hidden(sK11(sK1,sK2,sK0),sK2) | spl13_1),
% 2.18/0.66    inference(resolution,[],[f308,f83])).
% 2.18/0.66  fof(f308,plain,(
% 2.18/0.66    ~r2_hidden(sK11(sK1,sK2,sK0),k3_xboole_0(sK2,sK4)) | spl13_1),
% 2.18/0.66    inference(avatar_component_clause,[],[f306])).
% 2.18/0.66  fof(f313,plain,(
% 2.18/0.66    ~spl13_1 | ~spl13_2),
% 2.18/0.66    inference(avatar_split_clause,[],[f304,f310,f306])).
% 2.18/0.66  fof(f304,plain,(
% 2.18/0.66    ~r2_hidden(sK10(sK1,sK2,sK0),k3_xboole_0(sK1,sK3)) | ~r2_hidden(sK11(sK1,sK2,sK0),k3_xboole_0(sK2,sK4))),
% 2.18/0.66    inference(trivial_inequality_removal,[],[f298])).
% 2.18/0.66  fof(f298,plain,(
% 2.18/0.66    sK0 != sK0 | ~r2_hidden(sK10(sK1,sK2,sK0),k3_xboole_0(sK1,sK3)) | ~r2_hidden(sK11(sK1,sK2,sK0),k3_xboole_0(sK2,sK4))),
% 2.18/0.66    inference(superposition,[],[f39,f91])).
% 2.18/0.66  fof(f39,plain,(
% 2.18/0.66    ( ! [X6,X5] : (k4_tarski(X5,X6) != sK0 | ~r2_hidden(X5,k3_xboole_0(sK1,sK3)) | ~r2_hidden(X6,k3_xboole_0(sK2,sK4))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f14])).
% 2.18/0.66  % SZS output end Proof for theBenchmark
% 2.18/0.66  % (19116)------------------------------
% 2.18/0.66  % (19116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.66  % (19116)Termination reason: Refutation
% 2.18/0.66  
% 2.18/0.66  % (19116)Memory used [KB]: 11129
% 2.18/0.66  % (19116)Time elapsed: 0.207 s
% 2.18/0.66  % (19116)------------------------------
% 2.18/0.66  % (19116)------------------------------
% 2.18/0.66  % (19114)Success in time 0.289 s
%------------------------------------------------------------------------------
