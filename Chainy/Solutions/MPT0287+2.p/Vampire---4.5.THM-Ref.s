%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0287+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:22 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   35 (  59 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 288 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2764,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2763,f715])).

fof(f715,plain,(
    ~ r1_tarski(k3_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f569])).

fof(f569,plain,
    ( ~ r1_tarski(k3_tarski(sK4),sK5)
    & ! [X2] :
        ( r1_tarski(X2,sK5)
        | ~ r2_hidden(X2,sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f394,f568])).

fof(f568,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),X1)
        & ! [X2] :
            ( r1_tarski(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_tarski(k3_tarski(sK4),sK5)
      & ! [X2] :
          ( r1_tarski(X2,sK5)
          | ~ r2_hidden(X2,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f394,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      & ! [X2] :
          ( r1_tarski(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f386])).

fof(f386,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X2,X1) )
       => r1_tarski(k3_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f385])).

fof(f385,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f2763,plain,(
    r1_tarski(k3_tarski(sK4),sK5) ),
    inference(duplicate_literal_removal,[],[f2759])).

fof(f2759,plain,
    ( r1_tarski(k3_tarski(sK4),sK5)
    | r1_tarski(k3_tarski(sK4),sK5) ),
    inference(resolution,[],[f2687,f869])).

fof(f869,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f594])).

fof(f594,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f592,f593])).

fof(f593,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f592,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f591])).

fof(f591,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f441])).

fof(f441,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2687,plain,(
    ! [X3] :
      ( r2_hidden(sK11(k3_tarski(sK4),X3),sK5)
      | r1_tarski(k3_tarski(sK4),X3) ) ),
    inference(resolution,[],[f2682,f868])).

fof(f868,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f594])).

fof(f2682,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_tarski(sK4))
      | r2_hidden(X0,sK5) ) ),
    inference(duplicate_literal_removal,[],[f2661])).

fof(f2661,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_tarski(sK4))
      | r2_hidden(X0,sK5)
      | ~ r2_hidden(X0,k3_tarski(sK4)) ) ),
    inference(resolution,[],[f1943,f1258])).

fof(f1258,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK14(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f870])).

fof(f870,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK14(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f600])).

fof(f600,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK12(X0,X1),X3) )
            | ~ r2_hidden(sK12(X0,X1),X1) )
          & ( ( r2_hidden(sK13(X0,X1),X0)
              & r2_hidden(sK12(X0,X1),sK13(X0,X1)) )
            | r2_hidden(sK12(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK14(X0,X5),X0)
                & r2_hidden(X5,sK14(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f596,f599,f598,f597])).

fof(f597,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK12(X0,X1),X3) )
          | ~ r2_hidden(sK12(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK12(X0,X1),X4) )
          | r2_hidden(sK12(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f598,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK12(X0,X1),X4) )
     => ( r2_hidden(sK13(X0,X1),X0)
        & r2_hidden(sK12(X0,X1),sK13(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f599,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK14(X0,X5),X0)
        & r2_hidden(X5,sK14(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f596,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f595])).

fof(f595,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f286])).

fof(f286,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f1943,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK14(sK4,X2))
      | ~ r2_hidden(X2,k3_tarski(sK4))
      | r2_hidden(X3,sK5) ) ),
    inference(resolution,[],[f1676,f867])).

fof(f867,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f594])).

fof(f1676,plain,(
    ! [X3] :
      ( r1_tarski(sK14(sK4,X3),sK5)
      | ~ r2_hidden(X3,k3_tarski(sK4)) ) ),
    inference(resolution,[],[f714,f1257])).

fof(f1257,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK14(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f871])).

fof(f871,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK14(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f600])).

fof(f714,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK4)
      | r1_tarski(X2,sK5) ) ),
    inference(cnf_transformation,[],[f569])).
%------------------------------------------------------------------------------
