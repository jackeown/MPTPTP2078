%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0400+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:28 EST 2020

% Result     : Theorem 12.65s
% Output     : Refutation 12.65s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 123 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 504 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14980,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14958,f1028])).

fof(f1028,plain,(
    r2_hidden(sK4(sK1,sK3),sK1) ),
    inference(resolution,[],[f749,f752])).

fof(f752,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f660])).

fof(f660,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK4(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK5(X1,X4))
              & r2_hidden(sK5(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f657,f659,f658])).

fof(f658,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK4(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f659,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK5(X1,X4))
        & r2_hidden(sK5(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f657,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f656])).

fof(f656,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f579])).

fof(f579,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f545])).

fof(f545,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f749,plain,(
    ~ r1_setfam_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f655])).

fof(f655,plain,
    ( ~ r1_setfam_1(sK1,sK3)
    & r1_setfam_1(sK2,sK3)
    & r1_setfam_1(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f578,f654])).

fof(f654,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_setfam_1(X0,X2)
        & r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_setfam_1(sK1,sK3)
      & r1_setfam_1(sK2,sK3)
      & r1_setfam_1(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f578,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f577])).

fof(f577,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f563])).

fof(f563,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_setfam_1(X1,X2)
          & r1_setfam_1(X0,X1) )
       => r1_setfam_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f562])).

fof(f562,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).

fof(f14958,plain,(
    ~ r2_hidden(sK4(sK1,sK3),sK1) ),
    inference(resolution,[],[f14929,f1022])).

fof(f1022,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f747,f750])).

fof(f750,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK5(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f660])).

fof(f747,plain,(
    r1_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f655])).

fof(f14929,plain,(
    ~ r2_hidden(sK5(sK2,sK4(sK1,sK3)),sK2) ),
    inference(subsumption_resolution,[],[f14921,f1028])).

fof(f14921,plain,
    ( ~ r2_hidden(sK5(sK2,sK4(sK1,sK3)),sK2)
    | ~ r2_hidden(sK4(sK1,sK3),sK1) ),
    inference(resolution,[],[f9428,f1023])).

fof(f1023,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK5(sK2,X1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f747,f751])).

fof(f751,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK5(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f660])).

fof(f9428,plain,(
    ! [X116] :
      ( ~ r1_tarski(sK4(sK1,sK3),X116)
      | ~ r2_hidden(X116,sK2) ) ),
    inference(subsumption_resolution,[],[f9424,f1025])).

fof(f1025,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,X0),sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f748,f750])).

fof(f748,plain,(
    r1_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f655])).

fof(f9424,plain,(
    ! [X116] :
      ( ~ r2_hidden(X116,sK2)
      | ~ r1_tarski(sK4(sK1,sK3),X116)
      | ~ r2_hidden(sK5(sK3,X116),sK3) ) ),
    inference(resolution,[],[f1671,f1029])).

fof(f1029,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(sK1,sK3),X0)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f749,f753])).

fof(f753,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK4(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f660])).

fof(f1671,plain,(
    ! [X8,X7] :
      ( r1_tarski(X8,sK5(sK3,X7))
      | ~ r2_hidden(X7,sK2)
      | ~ r1_tarski(X8,X7) ) ),
    inference(resolution,[],[f1026,f765])).

fof(f765,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f592])).

fof(f592,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f591])).

fof(f591,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1026,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK5(sK3,X1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f748,f751])).
%------------------------------------------------------------------------------
