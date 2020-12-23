%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t103_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:57 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  94 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  168 ( 554 expanded)
%              Number of equality atoms :   43 ( 135 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1651,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1645,f28])).

fof(f28,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK3
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK3,sK0)
    & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
   => ( ! [X5,X4] :
          ( k4_tarski(X4,X5) != sK3
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK3,sK0)
      & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t103_zfmisc_1.p',t103_zfmisc_1)).

fof(f1645,plain,(
    ~ r2_hidden(sK3,sK0) ),
    inference(resolution,[],[f1644,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK1,sK2,X0),sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f22,f25,f24,f23])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X3
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t103_zfmisc_1.p',d2_zfmisc_1)).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t103_zfmisc_1.p',d3_tarski)).

fof(f27,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f1644,plain,(
    ~ r2_hidden(sK7(sK1,sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f1638,f28])).

fof(f1638,plain,
    ( ~ r2_hidden(sK7(sK1,sK2,sK3),sK1)
    | ~ r2_hidden(sK3,sK0) ),
    inference(resolution,[],[f1637,f80])).

fof(f80,plain,(
    ! [X1] :
      ( r2_hidden(sK8(sK1,sK2,X1),sK2)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f52,f43])).

fof(f43,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1637,plain,
    ( ~ r2_hidden(sK8(sK1,sK2,sK3),sK2)
    | ~ r2_hidden(sK7(sK1,sK2,sK3),sK1) ),
    inference(trivial_inequality_removal,[],[f1634])).

fof(f1634,plain,
    ( sK3 != sK3
    | ~ r2_hidden(sK8(sK1,sK2,sK3),sK2)
    | ~ r2_hidden(sK7(sK1,sK2,sK3),sK1) ),
    inference(superposition,[],[f29,f1613])).

fof(f1613,plain,(
    k4_tarski(sK7(sK1,sK2,sK3),sK8(sK1,sK2,sK3)) = sK3 ),
    inference(resolution,[],[f81,f28])).

fof(f81,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k4_tarski(sK7(sK1,sK2,X2),sK8(sK1,sK2,X2)) = X2 ) ),
    inference(resolution,[],[f52,f42])).

fof(f42,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
