%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t72_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:13 EDT 2019

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 140 expanded)
%              Number of leaves         :    8 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 967 expanded)
%              Number of equality atoms :   51 ( 292 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4653,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4652,f51])).

fof(f51,plain,(
    r2_hidden(sK8(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3) ),
    inference(resolution,[],[f44,f48])).

fof(f48,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = sK4(X0,X1,X2)
              & r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
                & r2_hidden(sK8(X0,X1,X8),X1)
                & r2_hidden(sK7(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f25,f28,f27,f26])).

fof(f26,plain,(
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
              ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X3
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',d2_zfmisc_1)).

fof(f44,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',d3_zfmisc_1)).

fof(f30,plain,(
    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK0
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22])).

fof(f22,plain,
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

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',t72_mcart_1)).

fof(f4652,plain,(
    ~ r2_hidden(sK8(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3) ),
    inference(trivial_inequality_removal,[],[f4649])).

fof(f4649,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK8(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3) ),
    inference(superposition,[],[f4638,f52])).

fof(f52,plain,(
    k4_tarski(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK8(k2_zfmisc_1(sK1,sK2),sK3,sK0)) = sK0 ),
    inference(resolution,[],[f44,f47])).

fof(f47,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4638,plain,(
    ! [X15] :
      ( k4_tarski(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),X15) != sK0
      | ~ r2_hidden(X15,sK3) ) ),
    inference(subsumption_resolution,[],[f4637,f91])).

fof(f91,plain,(
    r2_hidden(sK7(sK1,sK2,sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1) ),
    inference(resolution,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f44,f49])).

fof(f4637,plain,(
    ! [X15] :
      ( k4_tarski(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),X15) != sK0
      | ~ r2_hidden(X15,sK3)
      | ~ r2_hidden(sK7(sK1,sK2,sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1) ) ),
    inference(subsumption_resolution,[],[f4631,f92])).

fof(f92,plain,(
    r2_hidden(sK8(sK1,sK2,sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2) ),
    inference(resolution,[],[f50,f48])).

fof(f4631,plain,(
    ! [X15] :
      ( k4_tarski(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),X15) != sK0
      | ~ r2_hidden(X15,sK3)
      | ~ r2_hidden(sK8(sK1,sK2,sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2)
      | ~ r2_hidden(sK7(sK1,sK2,sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1) ) ),
    inference(superposition,[],[f43,f93])).

fof(f93,plain,(
    k4_tarski(sK7(sK1,sK2,sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK8(sK1,sK2,sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0))) = sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0) ),
    inference(resolution,[],[f50,f47])).

fof(f43,plain,(
    ! [X6,X4,X5] :
      ( k4_tarski(k4_tarski(X4,X5),X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',d3_mcart_1)).

fof(f31,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
