%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0424+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 15.70s
% Output     : CNFRefutation 15.70s
% Verified   : 
% Statistics : Number of formulae       :   25 (  37 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f852,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f441])).

fof(f2032,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f852])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f673,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f674,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f673])).

fof(f1507,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f674])).

fof(f610,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f611,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X0)
          & r1_tarski(k3_tarski(X0),X1) )
       => r1_tarski(X2,X1) ) ),
    inference(negated_conjecture,[],[f610])).

fof(f1020,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f611])).

fof(f1021,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f1020])).

fof(f1384,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,X1)
        & r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
   => ( ~ r1_tarski(sK119,sK118)
      & r2_hidden(sK119,sK117)
      & r1_tarski(k3_tarski(sK117),sK118) ) ),
    introduced(choice_axiom,[])).

fof(f1385,plain,
    ( ~ r1_tarski(sK119,sK118)
    & r2_hidden(sK119,sK117)
    & r1_tarski(k3_tarski(sK117),sK118) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK117,sK118,sK119])],[f1021,f1384])).

fof(f2356,plain,(
    ~ r1_tarski(sK119,sK118) ),
    inference(cnf_transformation,[],[f1385])).

fof(f2355,plain,(
    r2_hidden(sK119,sK117) ),
    inference(cnf_transformation,[],[f1385])).

fof(f2354,plain,(
    r1_tarski(k3_tarski(sK117),sK118) ),
    inference(cnf_transformation,[],[f1385])).

cnf(c_632,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f2032])).

cnf(c_48017,plain,
    ( r1_tarski(sK119,k3_tarski(sK117))
    | ~ r2_hidden(sK119,sK117) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1507])).

cnf(c_42106,plain,
    ( ~ r1_tarski(X0,sK118)
    | ~ r1_tarski(sK119,X0)
    | r1_tarski(sK119,sK118) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_46269,plain,
    ( ~ r1_tarski(k3_tarski(sK117),sK118)
    | ~ r1_tarski(sK119,k3_tarski(sK117))
    | r1_tarski(sK119,sK118) ),
    inference(instantiation,[status(thm)],[c_42106])).

cnf(c_952,negated_conjecture,
    ( ~ r1_tarski(sK119,sK118) ),
    inference(cnf_transformation,[],[f2356])).

cnf(c_953,negated_conjecture,
    ( r2_hidden(sK119,sK117) ),
    inference(cnf_transformation,[],[f2355])).

cnf(c_954,negated_conjecture,
    ( r1_tarski(k3_tarski(sK117),sK118) ),
    inference(cnf_transformation,[],[f2354])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48017,c_46269,c_952,c_953,c_954])).

%------------------------------------------------------------------------------
