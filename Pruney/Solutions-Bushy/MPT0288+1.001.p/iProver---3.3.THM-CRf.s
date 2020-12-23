%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0288+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:56 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   49 (  87 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  176 ( 390 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f15,f14,f13])).

fof(f24,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f9,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f23,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK4),k3_tarski(sK5))
      & r1_tarski(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(k3_tarski(sK4),k3_tarski(sK5))
    & r1_tarski(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f6,f17])).

fof(f29,plain,(
    ~ r1_tarski(k3_tarski(sK4),k3_tarski(sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1011,plain,
    ( ~ r2_hidden(X0,sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))))
    | r2_hidden(X0,k3_tarski(X1))
    | ~ r2_hidden(sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))),X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2841,plain,
    ( ~ r2_hidden(sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))),X0)
    | ~ r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))))
    | r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_4300,plain,
    ( ~ r2_hidden(sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))),sK5)
    | ~ r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))))
    | r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_573,plain,
    ( r2_hidden(sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))),X0)
    | ~ r2_hidden(sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))),sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1036,plain,
    ( r2_hidden(sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))),sK5)
    | ~ r2_hidden(sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))),sK4)
    | ~ r1_tarski(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_8,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_512,plain,
    ( r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))))
    | ~ r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_513,plain,
    ( r2_hidden(sK3(sK4,sK0(k3_tarski(sK4),k3_tarski(sK5))),sK4)
    | ~ r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(sK4),k3_tarski(sK5)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_158,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_tarski(sK5) != X1
    | k3_tarski(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_159,plain,
    ( ~ r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),k3_tarski(sK5)) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_151,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_tarski(sK5) != X1
    | k3_tarski(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_152,plain,
    ( r2_hidden(sK0(k3_tarski(sK4),k3_tarski(sK5)),k3_tarski(sK4)) ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4300,c_1036,c_512,c_513,c_159,c_152,c_10])).


%------------------------------------------------------------------------------
