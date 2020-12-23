%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0598+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Theorem 19.62s
% Output     : CNFRefutation 19.62s
% Verified   : 
% Statistics : Number of formulae       :   33 (  54 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 200 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f879,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1581,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f879])).

fof(f1582,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1581])).

fof(f1583,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1584,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1582,f1583])).

fof(f2042,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1584])).

fof(f647,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1308,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f647])).

fof(f1961,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1308])).

fof(f3076,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1961])).

fof(f796,conjecture,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f797,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f796])).

fof(f1480,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f797])).

fof(f1481,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1480])).

fof(f2020,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
     => ( ~ r2_hidden(sK164,X0)
        & r2_hidden(sK164,k2_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2019,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,k2_relat_1(X1)) )
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,sK162)
          & r2_hidden(X2,k2_relat_1(sK163)) )
      & v5_relat_1(sK163,sK162)
      & v1_relat_1(sK163) ) ),
    introduced(choice_axiom,[])).

fof(f2021,plain,
    ( ~ r2_hidden(sK164,sK162)
    & r2_hidden(sK164,k2_relat_1(sK163))
    & v5_relat_1(sK163,sK162)
    & v1_relat_1(sK163) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK162,sK163,sK164])],[f1481,f2020,f2019])).

fof(f3264,plain,(
    v5_relat_1(sK163,sK162) ),
    inference(cnf_transformation,[],[f2021])).

fof(f3266,plain,(
    ~ r2_hidden(sK164,sK162) ),
    inference(cnf_transformation,[],[f2021])).

fof(f3265,plain,(
    r2_hidden(sK164,k2_relat_1(sK163)) ),
    inference(cnf_transformation,[],[f2021])).

fof(f3263,plain,(
    v1_relat_1(sK163) ),
    inference(cnf_transformation,[],[f2021])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f2042])).

cnf(c_63288,plain,
    ( ~ r1_tarski(k2_relat_1(sK163),X0)
    | r2_hidden(sK164,X0)
    | ~ r2_hidden(sK164,k2_relat_1(sK163)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_72480,plain,
    ( ~ r1_tarski(k2_relat_1(sK163),sK162)
    | ~ r2_hidden(sK164,k2_relat_1(sK163))
    | r2_hidden(sK164,sK162) ),
    inference(instantiation,[status(thm)],[c_63288])).

cnf(c_1029,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3076])).

cnf(c_1217,negated_conjecture,
    ( v5_relat_1(sK163,sK162) ),
    inference(cnf_transformation,[],[f3264])).

cnf(c_13433,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK163 != X0
    | sK162 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1029,c_1217])).

cnf(c_13434,plain,
    ( r1_tarski(k2_relat_1(sK163),sK162)
    | ~ v1_relat_1(sK163) ),
    inference(unflattening,[status(thm)],[c_13433])).

cnf(c_1215,negated_conjecture,
    ( ~ r2_hidden(sK164,sK162) ),
    inference(cnf_transformation,[],[f3266])).

cnf(c_1216,negated_conjecture,
    ( r2_hidden(sK164,k2_relat_1(sK163)) ),
    inference(cnf_transformation,[],[f3265])).

cnf(c_1218,negated_conjecture,
    ( v1_relat_1(sK163) ),
    inference(cnf_transformation,[],[f3263])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_72480,c_13434,c_1215,c_1216,c_1218])).

%------------------------------------------------------------------------------
