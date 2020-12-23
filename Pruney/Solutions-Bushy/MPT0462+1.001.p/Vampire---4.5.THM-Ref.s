%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0462+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:02 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 247 expanded)
%              Number of leaves         :   12 (  81 expanded)
%              Depth                    :   26
%              Number of atoms          :  478 (1721 expanded)
%              Number of equality atoms :   11 (  54 expanded)
%              Maximal formula depth    :   17 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f868,plain,(
    $false ),
    inference(subsumption_resolution,[],[f867,f31])).

fof(f31,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(sK0,X1)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(sK0,sK1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
            & r1_tarski(X2,X3)
            & r1_tarski(sK0,sK1)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
          & r1_tarski(sK2,X3)
          & r1_tarski(sK0,sK1)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
        & r1_tarski(sK2,X3)
        & r1_tarski(sK0,sK1)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(f867,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f866,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f866,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f865,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f865,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f864,f32])).

fof(f32,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f864,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f863,f29])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f863,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f854,f30])).

fof(f30,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f854,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f675,f33])).

fof(f33,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f675,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_tarski(k5_relat_1(X7,X8),k5_relat_1(X9,X10))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X8)
      | ~ r1_tarski(X8,X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X7,X9) ) ),
    inference(subsumption_resolution,[],[f671,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f671,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_tarski(k5_relat_1(X7,X8),k5_relat_1(X9,X10))
      | ~ v1_relat_1(k5_relat_1(X7,X8))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X8)
      | ~ r1_tarski(X8,X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X7,X9) ) ),
    inference(duplicate_literal_removal,[],[f670])).

fof(f670,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_tarski(k5_relat_1(X7,X8),k5_relat_1(X9,X10))
      | ~ v1_relat_1(k5_relat_1(X7,X8))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X8)
      | ~ r1_tarski(X8,X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ r1_tarski(X7,X9) ) ),
    inference(resolution,[],[f577,f609])).

fof(f609,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X5) ) ),
    inference(subsumption_resolution,[],[f606,f43])).

fof(f606,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X5)
      | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X5) ) ),
    inference(duplicate_literal_removal,[],[f599])).

fof(f599,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X5)
      | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X5)
      | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7)) ) ),
    inference(resolution,[],[f381,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f381,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X2,k5_relat_1(X1,X0)),sK9(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0))
      | ~ v1_relat_1(X1)
      | r1_tarski(X2,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X3,X1) ) ),
    inference(subsumption_resolution,[],[f380,f43])).

fof(f380,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(X2,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k4_tarski(sK8(X2,k5_relat_1(X1,X0)),sK9(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0))
      | ~ r1_tarski(X3,X1)
      | ~ v1_relat_1(k5_relat_1(X3,X0)) ) ),
    inference(duplicate_literal_removal,[],[f369])).

fof(f369,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(X2,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k4_tarski(sK8(X2,k5_relat_1(X1,X0)),sK9(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0))
      | ~ r1_tarski(X3,X1)
      | ~ r2_hidden(k4_tarski(sK8(X2,k5_relat_1(X1,X0)),sK9(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0))
      | ~ v1_relat_1(k5_relat_1(X3,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f110,f45])).

fof(f45,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f110,plain,(
    ! [X14,X19,X17,X15,X18,X16] :
      ( ~ r2_hidden(k4_tarski(sK7(X14,X15,sK8(X16,k5_relat_1(X17,X18)),X19),sK9(X16,k5_relat_1(X17,X18))),X18)
      | ~ v1_relat_1(X18)
      | ~ v1_relat_1(X17)
      | r1_tarski(X16,k5_relat_1(X17,X18))
      | ~ v1_relat_1(X16)
      | ~ v1_relat_1(X15)
      | ~ v1_relat_1(X14)
      | ~ r2_hidden(k4_tarski(sK8(X16,k5_relat_1(X17,X18)),X19),k5_relat_1(X14,X15))
      | ~ r1_tarski(X14,X17) ) ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ r1_tarski(X2,X4) ) ),
    inference(subsumption_resolution,[],[f58,f43])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X4)
      | ~ r1_tarski(X2,X4) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X4)
      | ~ r1_tarski(X2,X4)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X1,k5_relat_1(X2,X3)),X0),X2)
      | ~ r2_hidden(k4_tarski(X0,sK9(X1,k5_relat_1(X2,X3))),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r1_tarski(X1,k5_relat_1(X2,X3))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK9(X1,k5_relat_1(X2,X3))),X3)
      | ~ r2_hidden(k4_tarski(sK8(X1,k5_relat_1(X2,X3)),X0),X2)
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r1_tarski(X1,k5_relat_1(X2,X3))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f577,plain,(
    ! [X21,X19,X22,X20] :
      ( ~ r1_tarski(X20,k5_relat_1(X19,X22))
      | r1_tarski(X20,k5_relat_1(X19,X21))
      | ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | ~ r1_tarski(X22,X21)
      | ~ v1_relat_1(X19) ) ),
    inference(duplicate_literal_removal,[],[f576])).

fof(f576,plain,(
    ! [X21,X19,X22,X20] :
      ( ~ v1_relat_1(X19)
      | r1_tarski(X20,k5_relat_1(X19,X21))
      | ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | ~ r1_tarski(X22,X21)
      | ~ r1_tarski(X20,k5_relat_1(X19,X22))
      | ~ v1_relat_1(X20)
      | r1_tarski(X20,k5_relat_1(X19,X21)) ) ),
    inference(resolution,[],[f233,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X2)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X2)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f40,f41])).

fof(f233,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(k4_tarski(sK8(X10,k5_relat_1(X9,X8)),sK9(X10,k5_relat_1(X9,X8))),k5_relat_1(X9,X11))
      | ~ v1_relat_1(X9)
      | r1_tarski(X10,k5_relat_1(X9,X8))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X11)
      | ~ r1_tarski(X11,X8) ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | r1_tarski(X10,k5_relat_1(X9,X8))
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK8(X10,k5_relat_1(X9,X8)),sK9(X10,k5_relat_1(X9,X8))),k5_relat_1(X9,X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X9)
      | ~ r2_hidden(k4_tarski(sK8(X10,k5_relat_1(X9,X8)),sK9(X10,k5_relat_1(X9,X8))),k5_relat_1(X9,X11))
      | ~ r1_tarski(X11,X8) ) ),
    inference(resolution,[],[f117,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ r1_tarski(X3,X4) ) ),
    inference(subsumption_resolution,[],[f52,f43])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X4)
      | ~ r1_tarski(X3,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f45,f40])).

fof(f117,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ r2_hidden(k4_tarski(sK7(X2,X3,sK8(X4,k5_relat_1(X2,X5)),X6),sK9(X4,k5_relat_1(X2,X5))),X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X2)
      | r1_tarski(X4,k5_relat_1(X2,X5))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(sK8(X4,k5_relat_1(X2,X5)),X6),k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ r2_hidden(k4_tarski(sK7(X2,X3,sK8(X4,k5_relat_1(X2,X5)),X6),sK9(X4,k5_relat_1(X2,X5))),X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X2)
      | r1_tarski(X4,k5_relat_1(X2,X5))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(sK8(X4,k5_relat_1(X2,X5)),X6),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ r2_hidden(k4_tarski(sK7(X2,X3,sK8(X4,k5_relat_1(X2,X5)),X6),sK9(X4,k5_relat_1(X2,X5))),X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X2)
      | r1_tarski(X4,k5_relat_1(X2,X5))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(sK8(X4,k5_relat_1(X2,X5)),X6),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f63,f46])).

%------------------------------------------------------------------------------
