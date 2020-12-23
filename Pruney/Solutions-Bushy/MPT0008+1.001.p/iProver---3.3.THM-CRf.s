%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0008+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:14 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   33 (  74 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 248 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
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
    inference(nnf_transformation,[],[f4])).

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

fof(f13,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X2)
        & r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK1,sK3)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ r1_tarski(sK1,sK3)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f11])).

fof(f18,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_133,plain,
    ( ~ r2_hidden(X0_35,X0_34)
    | r2_hidden(X0_35,X1_34)
    | ~ r1_tarski(X0_34,X1_34) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_166,plain,
    ( r2_hidden(sK0(sK1,sK3),X0_34)
    | ~ r2_hidden(sK0(sK1,sK3),sK1)
    | ~ r1_tarski(sK1,X0_34) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_189,plain,
    ( r2_hidden(sK0(sK1,sK3),sK2)
    | ~ r2_hidden(sK0(sK1,sK3),sK1)
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_170,plain,
    ( ~ r2_hidden(sK0(sK1,sK3),X0_34)
    | r2_hidden(sK0(sK1,sK3),X1_34)
    | ~ r1_tarski(X0_34,X1_34) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_173,plain,
    ( ~ r2_hidden(sK0(sK1,sK3),X0_34)
    | r2_hidden(sK0(sK1,sK3),sK3)
    | ~ r1_tarski(X0_34,sK3) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_177,plain,
    ( ~ r2_hidden(sK0(sK1,sK3),sK2)
    | r2_hidden(sK0(sK1,sK3),sK3)
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_3,negated_conjecture,
    ( ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_90,plain,
    ( ~ r2_hidden(sK0(sK1,sK3),sK3) ),
    inference(resolution,[status(thm)],[c_0,c_3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_84,plain,
    ( r2_hidden(sK0(sK1,sK3),sK1) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_189,c_177,c_90,c_84,c_4,c_5])).


%------------------------------------------------------------------------------
