%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0396+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:12 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 113 expanded)
%              Number of clauses        :   27 (  29 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  221 ( 469 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f31,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK0(X1,X2))
        & r2_hidden(sK0(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK0(X1,X2))
            & r2_hidden(sK0(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK0(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK5),k3_tarski(sK6))
      & r1_setfam_1(sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(k3_tarski(sK5),k3_tarski(sK6))
    & r1_setfam_1(sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f9,f22])).

fof(f35,plain,(
    r1_setfam_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X1,X2),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK4(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK4(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f30,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ~ r1_tarski(k3_tarski(sK5),k3_tarski(sK6)) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_912,plain,
    ( ~ r2_hidden(X0,sK0(sK6,sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6)))))
    | r2_hidden(X0,k3_tarski(sK6))
    | ~ r2_hidden(sK0(sK6,sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1562,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),sK0(sK6,sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),k3_tarski(sK6))
    | ~ r2_hidden(sK0(sK6,sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_806,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),X0)
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))))
    | ~ r1_tarski(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1054,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),sK0(sK6,sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6)))))
    | ~ r1_tarski(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))),sK0(sK6,sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))))) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_0,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r1_tarski(X2,sK0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,negated_conjecture,
    ( r1_setfam_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_160,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,sK0(X2,X0))
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_161,plain,
    ( ~ r2_hidden(X0,sK5)
    | r1_tarski(X0,sK0(sK6,X0)) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_832,plain,
    ( ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))),sK5)
    | r1_tarski(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))),sK0(sK6,sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))))) ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_1,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK0(X1,X2),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_148,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2,X0),X2)
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_149,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK0(sK6,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_833,plain,
    ( ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))),sK5)
    | r2_hidden(sK0(sK6,sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_10,plain,
    ( r2_hidden(X0,sK4(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_769,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK4(X1,X0),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_770,plain,
    ( r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6))),sK5)
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(sK5),k3_tarski(sK6)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_211,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | k3_tarski(sK6) != X1
    | k3_tarski(sK5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_212,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),k3_tarski(sK6)) ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_204,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k3_tarski(sK6) != X1
    | k3_tarski(sK5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_205,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6)),k3_tarski(sK5)) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1562,c_1054,c_832,c_833,c_769,c_770,c_212,c_205])).


%------------------------------------------------------------------------------
