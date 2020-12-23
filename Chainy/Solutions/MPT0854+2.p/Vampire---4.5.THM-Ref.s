%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0854+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   31 (  79 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 479 expanded)
%              Number of equality atoms :   40 ( 130 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5337,plain,(
    $false ),
    inference(global_subsumption,[],[f1601,f5181,f5259])).

fof(f5259,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(backward_demodulation,[],[f1997,f5127])).

fof(f5127,plain,(
    k2_mcart_1(sK0) = sK27(sK1,sK2,sK0) ),
    inference(superposition,[],[f1603,f1998])).

fof(f1998,plain,(
    sK0 = k4_tarski(sK26(sK1,sK2,sK0),sK27(sK1,sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f1600,f1912])).

fof(f1912,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK26(X0,X1,X8),sK27(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1696])).

fof(f1696,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK26(X0,X1,X8),sK27(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1501])).

fof(f1501,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK23(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK23(X0,X1,X2),X2) )
          & ( ( sK23(X0,X1,X2) = k4_tarski(sK24(X0,X1,X2),sK25(X0,X1,X2))
              & r2_hidden(sK25(X0,X1,X2),X1)
              & r2_hidden(sK24(X0,X1,X2),X0) )
            | r2_hidden(sK23(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK26(X0,X1,X8),sK27(X0,X1,X8)) = X8
                & r2_hidden(sK27(X0,X1,X8),X1)
                & r2_hidden(sK26(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24,sK25,sK26,sK27])],[f1497,f1500,f1499,f1498])).

fof(f1498,plain,(
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
              ( k4_tarski(X4,X5) != sK23(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK23(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK23(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK23(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1499,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK23(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK23(X0,X1,X2) = k4_tarski(sK24(X0,X1,X2),sK25(X0,X1,X2))
        & r2_hidden(sK25(X0,X1,X2),X1)
        & r2_hidden(sK24(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1500,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK26(X0,X1,X8),sK27(X0,X1,X8)) = X8
        & r2_hidden(sK27(X0,X1,X8),X1)
        & r2_hidden(sK26(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1497,plain,(
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
    inference(rectify,[],[f1496])).

fof(f1496,plain,(
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
    inference(nnf_transformation,[],[f286])).

fof(f286,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f1600,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f1453])).

fof(f1453,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1309,f1452])).

fof(f1452,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1309,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1293])).

fof(f1293,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f1292])).

fof(f1292,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f1603,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1300])).

fof(f1300,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f1997,plain,(
    r2_hidden(sK27(sK1,sK2,sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f1600,f1913])).

fof(f1913,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK27(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1695])).

fof(f1695,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK27(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1501])).

fof(f5181,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f1996,f5126])).

fof(f5126,plain,(
    k1_mcart_1(sK0) = sK26(sK1,sK2,sK0) ),
    inference(superposition,[],[f1602,f1998])).

fof(f1602,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1300])).

fof(f1996,plain,(
    r2_hidden(sK26(sK1,sK2,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f1600,f1914])).

fof(f1914,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK26(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1694])).

fof(f1694,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK26(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1501])).

fof(f1601,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f1453])).
%------------------------------------------------------------------------------
