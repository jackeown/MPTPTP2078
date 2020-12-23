%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0574+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:38 EST 2020

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 122 expanded)
%              Number of clauses        :   26 (  29 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 ( 536 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f9])).

fof(f13,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13,f12,f11])).

fof(f23,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))
      & r1_tarski(sK4,sK5)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))
    & r1_tarski(sK4,sK5)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f8,f19])).

fof(f30,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f21,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ~ r1_tarski(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_1132,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,sK5))
    | ~ r2_hidden(sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK5)
    | ~ r2_hidden(k4_tarski(X0,sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_1825,plain,
    ( ~ r2_hidden(sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK5)
    | r2_hidden(sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)),sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_835,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),X0)
    | ~ r2_hidden(sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_999,plain,
    ( ~ r1_tarski(sK4,sK5)
    | r2_hidden(sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK5)
    | ~ r2_hidden(sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_278,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_11])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_790,plain,
    ( r2_hidden(sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK4)
    | ~ r2_hidden(sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK4)) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_266,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(X0,sK2(sK6,X1,X0)),sK6) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_791,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK4))
    | r2_hidden(k4_tarski(sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)),sK2(sK6,sK4,sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_165,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | k10_relat_1(sK6,sK5) != X1
    | k10_relat_1(sK6,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_166,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_158,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | k10_relat_1(sK6,sK5) != X1
    | k10_relat_1(sK6,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_159,plain,
    ( r2_hidden(sK3(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK4)) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1825,c_999,c_790,c_791,c_166,c_159,c_10])).


%------------------------------------------------------------------------------
