%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t83_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:14 EDT 2019

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   48 (  79 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   19
%              Number of atoms          :  236 ( 515 expanded)
%              Number of equality atoms :   63 ( 140 expanded)
%              Maximal formula depth    :   18 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(subsumption_resolution,[],[f221,f69])).

fof(f69,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t83_mcart_1.p',d4_zfmisc_1)).

fof(f44,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ! [X5,X6,X7,X8] :
        ( k4_mcart_1(X5,X6,X7,X8) != sK0
        | ~ r2_hidden(X8,sK4)
        | ~ r2_hidden(X7,sK3)
        | ~ r2_hidden(X6,sK2)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6,X7,X8] :
            ( k4_mcart_1(X5,X6,X7,X8) != X0
            | ~ r2_hidden(X8,X4)
            | ~ r2_hidden(X7,X3)
            | ~ r2_hidden(X6,X2)
            | ~ r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) )
   => ( ! [X8,X7,X6,X5] :
          ( k4_mcart_1(X5,X6,X7,X8) != sK0
          | ~ r2_hidden(X8,sK4)
          | ~ r2_hidden(X7,sK3)
          | ~ r2_hidden(X6,sK2)
          | ~ r2_hidden(X5,sK1) )
      & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t83_mcart_1.p',t83_mcart_1)).

fof(f221,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)) ),
    inference(equality_resolution,[],[f220])).

fof(f220,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4))
      | ~ r2_hidden(X0,k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)) ) ),
    inference(resolution,[],[f218,f74])).

fof(f74,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK6(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = sK6(X0,X1,X2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f37,f40,f39,f38])).

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X3
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
        & r2_hidden(sK10(X0,X1,X8),X1)
        & r2_hidden(sK9(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/mcart_1__t83_mcart_1.p',d2_zfmisc_1)).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X1,sK4,X0),k3_zfmisc_1(sK1,sK2,sK3))
      | sK0 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK4)) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | ~ r2_hidden(sK9(X1,sK4,X0),k3_zfmisc_1(sK1,sK2,sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK4))
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK4)) ) ),
    inference(resolution,[],[f216,f73])).

fof(f73,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1,X2),sK4)
      | sK0 != X2
      | ~ r2_hidden(sK9(X0,X1,X2),k3_zfmisc_1(sK1,sK2,sK3))
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f215,f72])).

fof(f72,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f215,plain,(
    ! [X0,X1] :
      ( k4_tarski(X1,X0) != sK0
      | ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X1,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK4)
      | k4_tarski(X1,X0) != sK0
      | ~ r2_hidden(X1,k3_zfmisc_1(sK1,sK2,sK3))
      | ~ r2_hidden(X1,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    inference(resolution,[],[f213,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK11(X0,X1,X2,X3),X1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k3_mcart_1(sK11(X0,X1,X2,X3),sK12(X0,X1,X2,X3),sK13(X0,X1,X2,X3)) = X0
        & r2_hidden(sK13(X0,X1,X2,X3),X3)
        & r2_hidden(sK12(X0,X1,X2,X3),X2)
        & r2_hidden(sK11(X0,X1,X2,X3),X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f31,f42])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k3_mcart_1(sK11(X0,X1,X2,X3),sK12(X0,X1,X2,X3),sK13(X0,X1,X2,X3)) = X0
        & r2_hidden(sK13(X0,X1,X2,X3),X3)
        & r2_hidden(sK12(X0,X1,X2,X3),X2)
        & r2_hidden(sK11(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t83_mcart_1.p',t72_mcart_1)).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK11(X0,X2,sK2,sK3),sK1)
      | ~ r2_hidden(X1,sK4)
      | k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X0,k3_zfmisc_1(X2,sK2,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(sK11(X0,X2,sK2,sK3),sK1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X2,sK2,sK3))
      | ~ r2_hidden(X0,k3_zfmisc_1(X2,sK2,sK3)) ) ),
    inference(resolution,[],[f211,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK12(X0,X1,X2,X3),X2)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f211,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK12(X1,X2,X3,sK3),sK2)
      | k4_tarski(X1,X0) != sK0
      | ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(sK11(X1,X2,X3,sK3),sK1)
      | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,sK4)
      | k4_tarski(X1,X0) != sK0
      | ~ r2_hidden(sK12(X1,X2,X3,sK3),sK2)
      | ~ r2_hidden(sK11(X1,X2,X3,sK3),sK1)
      | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,sK3))
      | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,sK3)) ) ),
    inference(resolution,[],[f207,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK13(X0,X1,X2,X3),X3)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f207,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK13(X0,X1,X2,X3),sK3)
      | ~ r2_hidden(X4,sK4)
      | k4_tarski(X0,X4) != sK0
      | ~ r2_hidden(sK12(X0,X1,X2,X3),sK2)
      | ~ r2_hidden(sK11(X0,X1,X2,X3),sK1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(superposition,[],[f68,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK11(X0,X1,X2,X3),sK12(X0,X1,X2,X3),sK13(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_tarski(k3_mcart_1(X5,X6,X7),X8) != sK0
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t83_mcart_1.p',d4_mcart_1)).

fof(f45,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_mcart_1(X5,X6,X7,X8) != sK0
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
