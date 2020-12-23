%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0401+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:13 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   38 (  63 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 220 expanded)
%              Number of equality atoms :   38 (  38 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK1(X1,X2))
        & r2_hidden(sK1(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK1(X1,X2))
            & r2_hidden(sK1(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f12])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X1,X2),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r1_tarski(sK4,X0)
        & r2_hidden(sK4,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK2)
          & r2_hidden(X2,sK3) )
      & r1_setfam_1(sK3,k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_tarski(sK4,sK2)
    & r2_hidden(sK4,sK3)
    & r1_setfam_1(sK3,k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f7,f15,f14])).

fof(f23,plain,(
    r1_setfam_1(sK3,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK1(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ~ r1_tarski(sK4,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_348,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK2),sK4),k1_tarski(sK2))
    | sK1(k1_tarski(sK2),sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK1(X1,X2),X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,negated_conjecture,
    ( r1_setfam_1(sK3,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_128,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X0),X2)
    | k1_tarski(sK2) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_129,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK1(k1_tarski(sK2),X0),k1_tarski(sK2)) ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_345,plain,
    ( r2_hidden(sK1(k1_tarski(sK2),sK4),k1_tarski(sK2))
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_4,plain,
    ( ~ r1_setfam_1(X0,X1)
    | r1_tarski(X2,sK1(X1,X2))
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_101,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | sK1(X1,X2) != sK2
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_102,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(sK4,X0)
    | sK1(X1,sK4) != sK2 ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_120,plain,
    ( ~ r2_hidden(sK4,X0)
    | sK1(X1,sK4) != sK2
    | k1_tarski(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_102,c_8])).

cnf(c_121,plain,
    ( ~ r2_hidden(sK4,sK3)
    | sK1(k1_tarski(sK2),sK4) != sK2 ),
    inference(unflattening,[status(thm)],[c_120])).

cnf(c_7,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_348,c_345,c_121,c_7])).


%------------------------------------------------------------------------------
