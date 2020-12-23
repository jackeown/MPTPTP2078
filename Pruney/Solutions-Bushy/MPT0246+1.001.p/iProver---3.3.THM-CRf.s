%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0246+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:49 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   32 (  53 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 182 expanded)
%              Number of equality atoms :   76 ( 143 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f6])).

fof(f11,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK2 = X2
          | ~ r2_hidden(X2,sK1) )
      & k1_xboole_0 != sK1
      & k1_tarski(sK2) != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ! [X2] :
        ( sK2 = X2
        | ~ r2_hidden(X2,sK1) )
    & k1_xboole_0 != sK1
    & k1_tarski(sK2) != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f5,f8])).

fof(f14,plain,(
    ! [X2] :
      ( sK2 = X2
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    k1_tarski(sK2) != sK1 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_50,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_93,plain,
    ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_51,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_85,plain,
    ( sK0(sK1,sK2) != X0
    | sK0(sK1,sK2) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_92,plain,
    ( sK0(sK1,sK2) != sK0(sK1,sK2)
    | sK0(sK1,sK2) = sK2
    | sK2 != sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_0,plain,
    ( sK0(X0,X1) != X1
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_72,plain,
    ( sK0(sK1,X0) != X0
    | k1_tarski(X0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_84,plain,
    ( sK0(sK1,sK2) != sK2
    | k1_tarski(sK2) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_2,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | sK2 = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_32,plain,
    ( sK0(X0,X1) != X2
    | k1_tarski(X1) = X0
    | sK1 != X0
    | sK2 = X2
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_33,plain,
    ( k1_tarski(X0) = sK1
    | sK2 = sK0(sK1,X0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_32])).

cnf(c_3,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_35,plain,
    ( sK2 = sK0(sK1,X0)
    | k1_tarski(X0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_3])).

cnf(c_36,plain,
    ( k1_tarski(X0) = sK1
    | sK2 = sK0(sK1,X0) ),
    inference(renaming,[status(thm)],[c_35])).

cnf(c_71,plain,
    ( k1_tarski(sK2) = sK1
    | sK2 = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_4,negated_conjecture,
    ( k1_tarski(sK2) != sK1 ),
    inference(cnf_transformation,[],[f12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93,c_92,c_84,c_71,c_3,c_4])).


%------------------------------------------------------------------------------
