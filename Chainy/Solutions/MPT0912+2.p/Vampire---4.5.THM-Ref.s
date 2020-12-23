%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0912+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 38.22s
% Output     : Refutation 38.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 267 expanded)
%              Number of leaves         :   12 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 (1484 expanded)
%              Number of equality atoms :   66 ( 473 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35356,plain,(
    $false ),
    inference(subsumption_resolution,[],[f34900,f32975])).

fof(f32975,plain,(
    r2_hidden(sK29(sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f2064,f2711])).

fof(f2711,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK29(sK0),X0) ) ),
    inference(superposition,[],[f1900,f2353])).

fof(f2353,plain,(
    sK0 = k4_tarski(sK29(sK0),sK30(sK0)) ),
    inference(unit_resulting_resolution,[],[f2064,f1915])).

fof(f1915,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK29(X0),sK30(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1633])).

fof(f1633,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK29(X0),sK30(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29,sK30])],[f1465,f1632])).

fof(f1632,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK29(X0),sK30(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f1465,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f300])).

fof(f300,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f1900,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1624])).

fof(f1624,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1623])).

fof(f1623,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f318])).

fof(f318,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f2064,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f1701,f1746])).

fof(f1746,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f1701,plain,(
    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f1559])).

fof(f1559,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK0
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1390,f1558])).

fof(f1558,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5,X6] :
            ( k3_mcart_1(X4,X5,X6) != X0
            | ~ r2_hidden(X6,X3)
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) )
   => ( ! [X6,X5,X4] :
          ( k3_mcart_1(X4,X5,X6) != sK0
          | ~ r2_hidden(X6,sK3)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f1390,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1381])).

fof(f1381,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f1380])).

fof(f1380,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f34900,plain,(
    ~ r2_hidden(sK29(sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f2351,f33055,f33056,f33057,f2653])).

fof(f2653,plain,(
    ! [X37,X35,X36,X34] :
      ( ~ r2_hidden(sK35(X34,X35,X36),sK2)
      | ~ r2_hidden(X37,sK3)
      | sK0 != k4_tarski(X36,X37)
      | ~ r2_hidden(sK34(X34,X35,X36),sK1)
      | ~ r2_hidden(X36,k2_zfmisc_1(X34,X35)) ) ),
    inference(superposition,[],[f2063,f2263])).

fof(f2263,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK34(X0,X1,X8),sK35(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1918])).

fof(f1918,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK34(X0,X1,X8),sK35(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1639])).

fof(f1639,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK31(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK31(X0,X1,X2),X2) )
          & ( ( sK31(X0,X1,X2) = k4_tarski(sK32(X0,X1,X2),sK33(X0,X1,X2))
              & r2_hidden(sK33(X0,X1,X2),X1)
              & r2_hidden(sK32(X0,X1,X2),X0) )
            | r2_hidden(sK31(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK34(X0,X1,X8),sK35(X0,X1,X8)) = X8
                & r2_hidden(sK35(X0,X1,X8),X1)
                & r2_hidden(sK34(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31,sK32,sK33,sK34,sK35])],[f1635,f1638,f1637,f1636])).

fof(f1636,plain,(
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
              ( k4_tarski(X4,X5) != sK31(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK31(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK31(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK31(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1637,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK31(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK31(X0,X1,X2) = k4_tarski(sK32(X0,X1,X2),sK33(X0,X1,X2))
        & r2_hidden(sK33(X0,X1,X2),X1)
        & r2_hidden(sK32(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1638,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK34(X0,X1,X8),sK35(X0,X1,X8)) = X8
        & r2_hidden(sK35(X0,X1,X8),X1)
        & r2_hidden(sK34(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1635,plain,(
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
    inference(rectify,[],[f1634])).

fof(f1634,plain,(
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

fof(f2063,plain,(
    ! [X6,X4,X5] :
      ( sK0 != k4_tarski(k4_tarski(X4,X5),X6)
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(definition_unfolding,[],[f1702,f1717])).

fof(f1717,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1276])).

fof(f1276,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1702,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f1559])).

fof(f33057,plain,(
    r2_hidden(sK35(sK1,sK2,sK29(sK0)),sK2) ),
    inference(backward_demodulation,[],[f4194,f33000])).

fof(f33000,plain,(
    sK34(k2_zfmisc_1(sK1,sK2),sK3,sK0) = sK29(sK0) ),
    inference(unit_resulting_resolution,[],[f2352,f2718])).

fof(f2718,plain,(
    ! [X14,X15] :
      ( sK0 != k4_tarski(X14,X15)
      | sK29(sK0) = X14 ) ),
    inference(superposition,[],[f1910,f2353])).

fof(f1910,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f1462])).

fof(f1462,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f391])).

fof(f391,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f2352,plain,(
    sK0 = k4_tarski(sK34(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK35(k2_zfmisc_1(sK1,sK2),sK3,sK0)) ),
    inference(unit_resulting_resolution,[],[f2064,f2263])).

fof(f4194,plain,(
    r2_hidden(sK35(sK1,sK2,sK34(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2) ),
    inference(unit_resulting_resolution,[],[f2350,f2264])).

fof(f2264,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK35(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1917])).

fof(f1917,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK35(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1639])).

fof(f2350,plain,(
    r2_hidden(sK34(k2_zfmisc_1(sK1,sK2),sK3,sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f2064,f2265])).

fof(f2265,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK34(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1916])).

fof(f1916,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK34(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1639])).

fof(f33056,plain,(
    r2_hidden(sK34(sK1,sK2,sK29(sK0)),sK1) ),
    inference(backward_demodulation,[],[f4193,f33000])).

fof(f4193,plain,(
    r2_hidden(sK34(sK1,sK2,sK34(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f2350,f2265])).

fof(f33055,plain,(
    sK0 = k4_tarski(sK29(sK0),sK35(k2_zfmisc_1(sK1,sK2),sK3,sK0)) ),
    inference(backward_demodulation,[],[f2352,f33000])).

fof(f2351,plain,(
    r2_hidden(sK35(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3) ),
    inference(unit_resulting_resolution,[],[f2064,f2264])).
%------------------------------------------------------------------------------
