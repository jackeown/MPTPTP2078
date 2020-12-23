%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:24 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 129 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   21
%              Number of atoms          :  326 ( 794 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   17 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f612,plain,(
    $false ),
    inference(subsumption_resolution,[],[f611,f29])).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
                & r1_tarski(X0,X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X2))
              & r1_tarski(sK0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X2))
            & r1_tarski(sK0,X1)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X2))
          & r1_tarski(sK0,sK1)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X2))
        & r1_tarski(sK0,sK1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
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
               => ( r1_tarski(X0,X1)
                 => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).

fof(f611,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f610,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f610,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f609,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f609,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f604,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f604,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f603,f30])).

fof(f30,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f603,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X5) ) ),
    inference(subsumption_resolution,[],[f600,f40])).

fof(f40,plain,(
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

fof(f600,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X5)
      | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X5) ) ),
    inference(duplicate_literal_removal,[],[f593])).

fof(f593,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X5)
      | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X5)
      | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7)) ) ),
    inference(resolution,[],[f402,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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

fof(f402,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X2,k5_relat_1(X1,X0)),sK8(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0))
      | ~ v1_relat_1(X1)
      | r1_tarski(X2,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X3,X1) ) ),
    inference(subsumption_resolution,[],[f401,f40])).

fof(f401,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(X2,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k4_tarski(sK7(X2,k5_relat_1(X1,X0)),sK8(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0))
      | ~ r1_tarski(X3,X1)
      | ~ v1_relat_1(k5_relat_1(X3,X0)) ) ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(X2,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k4_tarski(sK7(X2,k5_relat_1(X1,X0)),sK8(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0))
      | ~ r1_tarski(X3,X1)
      | ~ r2_hidden(k4_tarski(sK7(X2,k5_relat_1(X1,X0)),sK8(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0))
      | ~ v1_relat_1(k5_relat_1(X3,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f103,f42])).

fof(f42,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f20,f19,f18])).

fof(f18,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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

fof(f103,plain,(
    ! [X14,X19,X17,X15,X18,X16] :
      ( ~ r2_hidden(k4_tarski(sK6(X14,X15,sK7(X16,k5_relat_1(X17,X18)),X19),sK8(X16,k5_relat_1(X17,X18))),X18)
      | ~ v1_relat_1(X18)
      | ~ v1_relat_1(X17)
      | r1_tarski(X16,k5_relat_1(X17,X18))
      | ~ v1_relat_1(X16)
      | ~ v1_relat_1(X15)
      | ~ v1_relat_1(X14)
      | ~ r2_hidden(k4_tarski(sK7(X16,k5_relat_1(X17,X18)),X19),k5_relat_1(X14,X15))
      | ~ r1_tarski(X14,X17) ) ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ r1_tarski(X2,X4) ) ),
    inference(subsumption_resolution,[],[f52,f40])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X4)
      | ~ r1_tarski(X2,X4) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X4)
      | ~ r1_tarski(X2,X4)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X1,k5_relat_1(X2,X3)),X0),X2)
      | ~ r2_hidden(k4_tarski(X0,sK8(X1,k5_relat_1(X2,X3))),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r1_tarski(X1,k5_relat_1(X2,X3))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f54,f40])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK8(X1,k5_relat_1(X2,X3))),X3)
      | ~ r2_hidden(k4_tarski(sK7(X1,k5_relat_1(X2,X3)),X0),X2)
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r1_tarski(X1,k5_relat_1(X2,X3))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:06:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (14391)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (14407)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.47  % (14398)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (14404)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (14403)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (14395)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (14393)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (14409)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (14409)Refutation not found, incomplete strategy% (14409)------------------------------
% 0.22/0.50  % (14409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14409)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (14409)Memory used [KB]: 10490
% 0.22/0.50  % (14409)Time elapsed: 0.079 s
% 0.22/0.50  % (14409)------------------------------
% 0.22/0.50  % (14409)------------------------------
% 0.22/0.50  % (14396)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (14394)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (14405)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (14397)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (14392)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (14389)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (14390)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14408)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (14401)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14390)Refutation not found, incomplete strategy% (14390)------------------------------
% 0.22/0.51  % (14390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14390)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (14390)Memory used [KB]: 10618
% 0.22/0.51  % (14390)Time elapsed: 0.095 s
% 0.22/0.51  % (14390)------------------------------
% 0.22/0.51  % (14390)------------------------------
% 0.22/0.52  % (14402)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (14399)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (14402)Refutation not found, incomplete strategy% (14402)------------------------------
% 0.22/0.52  % (14402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14402)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14402)Memory used [KB]: 1663
% 0.22/0.52  % (14402)Time elapsed: 0.095 s
% 0.22/0.52  % (14402)------------------------------
% 0.22/0.52  % (14402)------------------------------
% 0.22/0.53  % (14400)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.25/0.55  % (14406)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.54/0.63  % (14391)Refutation found. Thanks to Tanya!
% 1.54/0.63  % SZS status Theorem for theBenchmark
% 1.54/0.64  % SZS output start Proof for theBenchmark
% 1.54/0.64  fof(f612,plain,(
% 1.54/0.64    $false),
% 1.54/0.64    inference(subsumption_resolution,[],[f611,f29])).
% 1.54/0.64  fof(f29,plain,(
% 1.54/0.64    r1_tarski(sK0,sK1)),
% 1.54/0.64    inference(cnf_transformation,[],[f15])).
% 1.54/0.64  fof(f15,plain,(
% 1.54/0.64    ((~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.54/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13,f12])).
% 1.54/0.64  fof(f12,plain,(
% 1.54/0.64    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X2)) & r1_tarski(sK0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.54/0.64    introduced(choice_axiom,[])).
% 1.54/0.64  fof(f13,plain,(
% 1.54/0.64    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X2)) & r1_tarski(sK0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X2)) & r1_tarski(sK0,sK1) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.54/0.64    introduced(choice_axiom,[])).
% 1.54/0.64  fof(f14,plain,(
% 1.54/0.64    ? [X2] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X2)) & r1_tarski(sK0,sK1) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.54/0.64    introduced(choice_axiom,[])).
% 1.54/0.64  fof(f7,plain,(
% 1.54/0.64    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.54/0.64    inference(flattening,[],[f6])).
% 1.54/0.64  fof(f6,plain,(
% 1.54/0.64    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.54/0.64    inference(ennf_transformation,[],[f5])).
% 1.54/0.64  fof(f5,negated_conjecture,(
% 1.54/0.64    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 1.54/0.64    inference(negated_conjecture,[],[f4])).
% 1.54/0.64  fof(f4,conjecture,(
% 1.54/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 1.54/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).
% 1.54/0.64  fof(f611,plain,(
% 1.54/0.64    ~r1_tarski(sK0,sK1)),
% 1.54/0.64    inference(subsumption_resolution,[],[f610,f28])).
% 1.54/0.64  fof(f28,plain,(
% 1.54/0.64    v1_relat_1(sK2)),
% 1.54/0.64    inference(cnf_transformation,[],[f15])).
% 1.54/0.64  fof(f610,plain,(
% 1.54/0.64    ~v1_relat_1(sK2) | ~r1_tarski(sK0,sK1)),
% 1.54/0.64    inference(subsumption_resolution,[],[f609,f26])).
% 1.54/0.64  fof(f26,plain,(
% 1.54/0.64    v1_relat_1(sK0)),
% 1.54/0.64    inference(cnf_transformation,[],[f15])).
% 1.54/0.64  fof(f609,plain,(
% 1.54/0.64    ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~r1_tarski(sK0,sK1)),
% 1.54/0.64    inference(subsumption_resolution,[],[f604,f27])).
% 1.54/0.64  fof(f27,plain,(
% 1.54/0.64    v1_relat_1(sK1)),
% 1.54/0.64    inference(cnf_transformation,[],[f15])).
% 1.54/0.64  fof(f604,plain,(
% 1.54/0.64    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~r1_tarski(sK0,sK1)),
% 1.54/0.64    inference(resolution,[],[f603,f30])).
% 1.54/0.64  fof(f30,plain,(
% 1.54/0.64    ~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),
% 1.54/0.64    inference(cnf_transformation,[],[f15])).
% 1.54/0.64  fof(f603,plain,(
% 1.54/0.64    ( ! [X6,X7,X5] : (r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7)) | ~v1_relat_1(X5) | ~v1_relat_1(X6) | ~v1_relat_1(X7) | ~r1_tarski(X6,X5)) )),
% 1.54/0.64    inference(subsumption_resolution,[],[f600,f40])).
% 1.54/0.64  fof(f40,plain,(
% 1.54/0.64    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(cnf_transformation,[],[f11])).
% 1.54/0.64  fof(f11,plain,(
% 1.54/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(flattening,[],[f10])).
% 1.54/0.64  fof(f10,plain,(
% 1.54/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.54/0.64    inference(ennf_transformation,[],[f3])).
% 1.54/0.64  fof(f3,axiom,(
% 1.54/0.64    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.54/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.54/0.64  fof(f600,plain,(
% 1.54/0.64    ( ! [X6,X7,X5] : (~v1_relat_1(X5) | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X6) | ~v1_relat_1(X7) | ~r1_tarski(X6,X5)) )),
% 1.54/0.64    inference(duplicate_literal_removal,[],[f593])).
% 1.54/0.64  fof(f593,plain,(
% 1.54/0.64    ( ! [X6,X7,X5] : (~v1_relat_1(X5) | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X6) | ~v1_relat_1(X7) | ~r1_tarski(X6,X5) | r1_tarski(k5_relat_1(X6,X7),k5_relat_1(X5,X7)) | ~v1_relat_1(k5_relat_1(X6,X7))) )),
% 1.54/0.64    inference(resolution,[],[f402,f38])).
% 1.54/0.64  fof(f38,plain,(
% 1.54/0.64    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(cnf_transformation,[],[f25])).
% 1.54/0.64  fof(f25,plain,(
% 1.54/0.64    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f23,f24])).
% 1.54/0.64  fof(f24,plain,(
% 1.54/0.64    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)))),
% 1.54/0.64    introduced(choice_axiom,[])).
% 1.54/0.64  fof(f23,plain,(
% 1.54/0.64    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(rectify,[],[f22])).
% 1.54/0.64  fof(f22,plain,(
% 1.54/0.64    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(nnf_transformation,[],[f9])).
% 1.54/0.64  fof(f9,plain,(
% 1.54/0.64    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(ennf_transformation,[],[f1])).
% 1.54/0.64  fof(f1,axiom,(
% 1.54/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.54/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 1.54/0.64  fof(f402,plain,(
% 1.54/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK7(X2,k5_relat_1(X1,X0)),sK8(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0)) | ~v1_relat_1(X1) | r1_tarski(X2,k5_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_relat_1(X0) | ~r1_tarski(X3,X1)) )),
% 1.54/0.64    inference(subsumption_resolution,[],[f401,f40])).
% 1.54/0.64  fof(f401,plain,(
% 1.54/0.64    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(X2,k5_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~r2_hidden(k4_tarski(sK7(X2,k5_relat_1(X1,X0)),sK8(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0)) | ~r1_tarski(X3,X1) | ~v1_relat_1(k5_relat_1(X3,X0))) )),
% 1.54/0.64    inference(duplicate_literal_removal,[],[f390])).
% 1.54/0.64  fof(f390,plain,(
% 1.54/0.64    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(X2,k5_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | ~v1_relat_1(X3) | ~r2_hidden(k4_tarski(sK7(X2,k5_relat_1(X1,X0)),sK8(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0)) | ~r1_tarski(X3,X1) | ~r2_hidden(k4_tarski(sK7(X2,k5_relat_1(X1,X0)),sK8(X2,k5_relat_1(X1,X0))),k5_relat_1(X3,X0)) | ~v1_relat_1(k5_relat_1(X3,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X3)) )),
% 1.54/0.64    inference(resolution,[],[f103,f42])).
% 1.54/0.64  fof(f42,plain,(
% 1.54/0.64    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(equality_resolution,[],[f32])).
% 1.54/0.64  fof(f32,plain,(
% 1.54/0.64    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(cnf_transformation,[],[f21])).
% 1.54/0.64  fof(f21,plain,(
% 1.54/0.64    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f20,f19,f18])).
% 1.54/0.64  fof(f18,plain,(
% 1.54/0.64    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 1.54/0.64    introduced(choice_axiom,[])).
% 1.54/0.64  fof(f19,plain,(
% 1.54/0.64    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)))),
% 1.54/0.64    introduced(choice_axiom,[])).
% 1.54/0.64  fof(f20,plain,(
% 1.54/0.64    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)))),
% 1.54/0.64    introduced(choice_axiom,[])).
% 1.54/0.64  fof(f17,plain,(
% 1.54/0.64    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(rectify,[],[f16])).
% 1.54/0.64  fof(f16,plain,(
% 1.54/0.64    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(nnf_transformation,[],[f8])).
% 1.54/0.64  fof(f8,plain,(
% 1.54/0.64    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.64    inference(ennf_transformation,[],[f2])).
% 1.54/0.64  fof(f2,axiom,(
% 1.54/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.54/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 1.54/0.64  fof(f103,plain,(
% 1.54/0.64    ( ! [X14,X19,X17,X15,X18,X16] : (~r2_hidden(k4_tarski(sK6(X14,X15,sK7(X16,k5_relat_1(X17,X18)),X19),sK8(X16,k5_relat_1(X17,X18))),X18) | ~v1_relat_1(X18) | ~v1_relat_1(X17) | r1_tarski(X16,k5_relat_1(X17,X18)) | ~v1_relat_1(X16) | ~v1_relat_1(X15) | ~v1_relat_1(X14) | ~r2_hidden(k4_tarski(sK7(X16,k5_relat_1(X17,X18)),X19),k5_relat_1(X14,X15)) | ~r1_tarski(X14,X17)) )),
% 1.54/0.64    inference(resolution,[],[f57,f53])).
% 1.54/0.64  fof(f53,plain,(
% 1.54/0.64    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X4) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~r1_tarski(X2,X4)) )),
% 1.54/0.64    inference(subsumption_resolution,[],[f52,f40])).
% 1.54/0.64  fof(f52,plain,(
% 1.54/0.64    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~v1_relat_1(k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X4) | ~r1_tarski(X2,X4)) )),
% 1.54/0.64    inference(duplicate_literal_removal,[],[f51])).
% 1.54/0.64  fof(f51,plain,(
% 1.54/0.64    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~v1_relat_1(k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X4) | ~r1_tarski(X2,X4) | ~v1_relat_1(X2)) )),
% 1.54/0.64    inference(resolution,[],[f43,f37])).
% 1.54/0.64  fof(f37,plain,(
% 1.54/0.64    ( ! [X4,X0,X5,X1] : (~r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(cnf_transformation,[],[f25])).
% 1.54/0.64  fof(f43,plain,(
% 1.54/0.64    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(equality_resolution,[],[f31])).
% 1.54/0.64  fof(f31,plain,(
% 1.54/0.64    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(cnf_transformation,[],[f21])).
% 1.54/0.64  fof(f57,plain,(
% 1.54/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK7(X1,k5_relat_1(X2,X3)),X0),X2) | ~r2_hidden(k4_tarski(X0,sK8(X1,k5_relat_1(X2,X3))),X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r1_tarski(X1,k5_relat_1(X2,X3)) | ~v1_relat_1(X1)) )),
% 1.54/0.64    inference(subsumption_resolution,[],[f54,f40])).
% 1.54/0.64  fof(f54,plain,(
% 1.54/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,sK8(X1,k5_relat_1(X2,X3))),X3) | ~r2_hidden(k4_tarski(sK7(X1,k5_relat_1(X2,X3)),X0),X2) | ~v1_relat_1(k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r1_tarski(X1,k5_relat_1(X2,X3)) | ~v1_relat_1(X1)) )),
% 1.54/0.64    inference(resolution,[],[f41,f39])).
% 1.54/0.64  fof(f39,plain,(
% 1.54/0.64    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(cnf_transformation,[],[f25])).
% 1.54/0.64  fof(f41,plain,(
% 1.54/0.64    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(equality_resolution,[],[f33])).
% 1.54/0.64  fof(f33,plain,(
% 1.54/0.64    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.64    inference(cnf_transformation,[],[f21])).
% 1.54/0.64  % SZS output end Proof for theBenchmark
% 1.54/0.64  % (14391)------------------------------
% 1.54/0.64  % (14391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.64  % (14391)Termination reason: Refutation
% 1.54/0.64  
% 1.54/0.64  % (14391)Memory used [KB]: 12025
% 1.54/0.64  % (14391)Time elapsed: 0.232 s
% 1.54/0.64  % (14391)------------------------------
% 1.54/0.64  % (14391)------------------------------
% 1.54/0.64  % (14380)Success in time 0.274 s
%------------------------------------------------------------------------------
