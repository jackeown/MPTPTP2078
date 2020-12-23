%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0855+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   31 (  69 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  144 ( 298 expanded)
%              Number of equality atoms :   47 (  96 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2406,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2405,f1648])).

fof(f1648,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f1483])).

fof(f1483,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    & sK0 = k4_tarski(sK3,sK4)
    & r2_hidden(k2_mcart_1(sK0),sK2)
    & r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1310,f1482,f1481])).

fof(f1481,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        & ? [X3,X4] : k4_tarski(X3,X4) = X0
        & r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
   => ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
      & ? [X4,X3] : k4_tarski(X3,X4) = sK0
      & r2_hidden(k2_mcart_1(sK0),sK2)
      & r2_hidden(k1_mcart_1(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1482,plain,
    ( ? [X4,X3] : k4_tarski(X3,X4) = sK0
   => sK0 = k4_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f1310,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f1309])).

fof(f1309,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f1294])).

fof(f1294,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) )
       => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
          | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    inference(negated_conjecture,[],[f1293])).

fof(f1293,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f2405,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f2402,f1647])).

fof(f1647,plain,(
    sK0 = k4_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f1483])).

fof(f2402,plain,(
    r2_hidden(k4_tarski(sK3,sK4),k2_zfmisc_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f2362,f2299])).

fof(f2299,plain,(
    k2_mcart_1(sK0) = sK4 ),
    inference(superposition,[],[f1778,f1647])).

fof(f1778,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1301])).

fof(f1301,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f2362,plain,(
    r2_hidden(k4_tarski(sK3,k2_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f2234,f2298])).

fof(f2298,plain,(
    k1_mcart_1(sK0) = sK3 ),
    inference(superposition,[],[f1777,f1647])).

fof(f1777,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1301])).

fof(f2234,plain,(
    r2_hidden(k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f1645,f1646,f1990])).

fof(f1990,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f1989])).

fof(f1989,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f1726])).

fof(f1726,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1518])).

fof(f1518,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK19(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK19(X0,X1,X2),X2) )
          & ( ( sK19(X0,X1,X2) = k4_tarski(sK20(X0,X1,X2),sK21(X0,X1,X2))
              & r2_hidden(sK21(X0,X1,X2),X1)
              & r2_hidden(sK20(X0,X1,X2),X0) )
            | r2_hidden(sK19(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK22(X0,X1,X8),sK23(X0,X1,X8)) = X8
                & r2_hidden(sK23(X0,X1,X8),X1)
                & r2_hidden(sK22(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21,sK22,sK23])],[f1514,f1517,f1516,f1515])).

fof(f1515,plain,(
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
              ( k4_tarski(X4,X5) != sK19(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK19(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK19(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK19(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1516,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK19(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK19(X0,X1,X2) = k4_tarski(sK20(X0,X1,X2),sK21(X0,X1,X2))
        & r2_hidden(sK21(X0,X1,X2),X1)
        & r2_hidden(sK20(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1517,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK22(X0,X1,X8),sK23(X0,X1,X8)) = X8
        & r2_hidden(sK23(X0,X1,X8),X1)
        & r2_hidden(sK22(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1514,plain,(
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
    inference(rectify,[],[f1513])).

fof(f1513,plain,(
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

fof(f1646,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(cnf_transformation,[],[f1483])).

fof(f1645,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f1483])).
%------------------------------------------------------------------------------
