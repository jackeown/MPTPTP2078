%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0771+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 43.33s
% Output     : CNFRefutation 43.33s
% Verified   : 
% Statistics : Number of formulae       :   35 (  65 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 227 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1152,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2287,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1152])).

fof(f2288,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2287])).

fof(f5049,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2288])).

fof(f5048,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2288])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1184,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f2333,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1184])).

fof(f2334,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2333])).

fof(f2335,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK21(X0,X1),X1)
        & r2_hidden(sK21(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2336,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK21(X0,X1),X1)
          & r2_hidden(sK21(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f2334,f2335])).

fof(f3100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK21(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2336])).

fof(f3099,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK21(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2336])).

fof(f1153,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1154,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f1153])).

fof(f2289,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1154])).

fof(f3084,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),sK289)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)) )
      & v1_relat_1(sK290) ) ),
    introduced(choice_axiom,[])).

fof(f3085,plain,
    ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),sK289)
      | ~ r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)) )
    & v1_relat_1(sK290) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK289,sK290])],[f2289,f3084])).

fof(f5051,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),sK289)
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)) ),
    inference(cnf_transformation,[],[f3085])).

fof(f5050,plain,(
    v1_relat_1(sK290) ),
    inference(cnf_transformation,[],[f3085])).

cnf(c_1943,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f5049])).

cnf(c_92682,plain,
    ( ~ r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),sK289),k3_relat_1(k2_wellord1(X0,sK289)))
    | r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),sK289),sK289)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_174613,plain,
    ( ~ r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),sK289),k3_relat_1(k2_wellord1(sK290,sK289)))
    | r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),sK289),sK289)
    | ~ v1_relat_1(sK290) ),
    inference(instantiation,[status(thm)],[c_92682])).

cnf(c_1944,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f5048])).

cnf(c_94902,plain,
    ( ~ r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)),k3_relat_1(k2_wellord1(sK290,X0)))
    | r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)),k3_relat_1(sK290))
    | ~ v1_relat_1(sK290) ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_145959,plain,
    ( ~ r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)),k3_relat_1(k2_wellord1(sK290,sK289)))
    | r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)),k3_relat_1(sK290))
    | ~ v1_relat_1(sK290) ),
    inference(instantiation,[status(thm)],[c_94902])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK21(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3100])).

cnf(c_90000,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290))
    | ~ r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)),k3_relat_1(sK290)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK21(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3099])).

cnf(c_90002,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290))
    | r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290)),k3_relat_1(k2_wellord1(sK290,sK289))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_89782,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),sK289)
    | ~ r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),sK289),sK289) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_89784,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),sK289)
    | r2_hidden(sK21(k3_relat_1(k2_wellord1(sK290,sK289)),sK289),k3_relat_1(k2_wellord1(sK290,sK289))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1945,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),k3_relat_1(sK290))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK290,sK289)),sK289) ),
    inference(cnf_transformation,[],[f5051])).

cnf(c_1946,negated_conjecture,
    ( v1_relat_1(sK290) ),
    inference(cnf_transformation,[],[f5050])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_174613,c_145959,c_90000,c_90002,c_89782,c_89784,c_1945,c_1946])).

%------------------------------------------------------------------------------
