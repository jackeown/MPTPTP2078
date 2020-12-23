%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0401+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 27.74s
% Output     : CNFRefutation 27.74s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 125 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f632,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f633,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f632])).

fof(f1405,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f633])).

fof(f563,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f564,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f563])).

fof(f942,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f564])).

fof(f1281,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r1_tarski(sK102,X0)
        & r2_hidden(sK102,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1280,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK100)
          & r2_hidden(X2,sK101) )
      & r1_setfam_1(sK101,k1_tarski(sK100)) ) ),
    introduced(choice_axiom,[])).

fof(f1282,plain,
    ( ~ r1_tarski(sK102,sK100)
    & r2_hidden(sK102,sK101)
    & r1_setfam_1(sK101,k1_tarski(sK100)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK100,sK101,sK102])],[f942,f1281,f1280])).

fof(f2178,plain,(
    r1_setfam_1(sK101,k1_tarski(sK100)) ),
    inference(cnf_transformation,[],[f1282])).

fof(f389,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1839,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f389])).

fof(f557,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f935,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f557])).

fof(f2172,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f935])).

fof(f441,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f811,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f441])).

fof(f1930,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f811])).

fof(f2180,plain,(
    ~ r1_tarski(sK102,sK100) ),
    inference(cnf_transformation,[],[f1282])).

fof(f2179,plain,(
    r2_hidden(sK102,sK101) ),
    inference(cnf_transformation,[],[f1282])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1405])).

cnf(c_30257,plain,
    ( ~ r1_tarski(X0,sK100)
    | ~ r1_tarski(sK102,X0)
    | r1_tarski(sK102,sK100) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_36062,plain,
    ( ~ r1_tarski(k3_tarski(X0),sK100)
    | ~ r1_tarski(sK102,k3_tarski(X0))
    | r1_tarski(sK102,sK100) ),
    inference(instantiation,[status(thm)],[c_30257])).

cnf(c_61840,plain,
    ( ~ r1_tarski(k3_tarski(sK101),sK100)
    | ~ r1_tarski(sK102,k3_tarski(sK101))
    | r1_tarski(sK102,sK100) ),
    inference(instantiation,[status(thm)],[c_36062])).

cnf(c_880,negated_conjecture,
    ( r1_setfam_1(sK101,k1_tarski(sK100)) ),
    inference(cnf_transformation,[],[f2178])).

cnf(c_22995,plain,
    ( r1_setfam_1(sK101,k1_tarski(sK100)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_541,plain,
    ( k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f1839])).

cnf(c_872,plain,
    ( ~ r1_setfam_1(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f2172])).

cnf(c_23003,plain,
    ( r1_setfam_1(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_30819,plain,
    ( r1_setfam_1(X0,k1_tarski(X1)) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_23003])).

cnf(c_58766,plain,
    ( r1_tarski(k3_tarski(sK101),sK100) = iProver_top ),
    inference(superposition,[status(thm)],[c_22995,c_30819])).

cnf(c_58773,plain,
    ( r1_tarski(k3_tarski(sK101),sK100) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_58766])).

cnf(c_632,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1930])).

cnf(c_29546,plain,
    ( r1_tarski(sK102,k3_tarski(sK101))
    | ~ r2_hidden(sK102,sK101) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_878,negated_conjecture,
    ( ~ r1_tarski(sK102,sK100) ),
    inference(cnf_transformation,[],[f2180])).

cnf(c_879,negated_conjecture,
    ( r2_hidden(sK102,sK101) ),
    inference(cnf_transformation,[],[f2179])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61840,c_58773,c_29546,c_878,c_879])).

%------------------------------------------------------------------------------
