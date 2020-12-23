%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0629+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 19.47s
% Output     : CNFRefutation 19.47s
% Verified   : 
% Statistics : Number of formulae       :   31 (  52 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 264 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f844,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1596,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f844])).

fof(f3502,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1596])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f934,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1710,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f934])).

fof(f1711,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1710])).

fof(f1712,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1713,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1711,f1712])).

fof(f2216,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1713])).

fof(f913,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f914,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f913])).

fof(f1683,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f914])).

fof(f1684,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1683])).

fof(f2202,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ~ r2_hidden(X0,k2_relat_1(X1))
        & r2_hidden(X0,k2_relat_1(k5_relat_1(sK184,X1)))
        & v1_funct_1(sK184)
        & v1_relat_1(sK184) ) ) ),
    introduced(choice_axiom,[])).

fof(f2201,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X0,k2_relat_1(X1))
            & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(sK182,k2_relat_1(sK183))
          & r2_hidden(sK182,k2_relat_1(k5_relat_1(X2,sK183)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK183)
      & v1_relat_1(sK183) ) ),
    introduced(choice_axiom,[])).

fof(f2203,plain,
    ( ~ r2_hidden(sK182,k2_relat_1(sK183))
    & r2_hidden(sK182,k2_relat_1(k5_relat_1(sK184,sK183)))
    & v1_funct_1(sK184)
    & v1_relat_1(sK184)
    & v1_funct_1(sK183)
    & v1_relat_1(sK183) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK182,sK183,sK184])],[f1684,f2202,f2201])).

fof(f3636,plain,(
    ~ r2_hidden(sK182,k2_relat_1(sK183)) ),
    inference(cnf_transformation,[],[f2203])).

fof(f3635,plain,(
    r2_hidden(sK182,k2_relat_1(k5_relat_1(sK184,sK183))) ),
    inference(cnf_transformation,[],[f2203])).

fof(f3633,plain,(
    v1_relat_1(sK184) ),
    inference(cnf_transformation,[],[f2203])).

fof(f3631,plain,(
    v1_relat_1(sK183) ),
    inference(cnf_transformation,[],[f2203])).

cnf(c_1280,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3502])).

cnf(c_65423,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK184,sK183)),k2_relat_1(sK183))
    | ~ v1_relat_1(sK184)
    | ~ v1_relat_1(sK183) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f2216])).

cnf(c_50809,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK184,sK183)),X0)
    | r2_hidden(sK182,X0)
    | ~ r2_hidden(sK182,k2_relat_1(k5_relat_1(sK184,sK183))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_65422,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK184,sK183)),k2_relat_1(sK183))
    | ~ r2_hidden(sK182,k2_relat_1(k5_relat_1(sK184,sK183)))
    | r2_hidden(sK182,k2_relat_1(sK183)) ),
    inference(instantiation,[status(thm)],[c_50809])).

cnf(c_1409,negated_conjecture,
    ( ~ r2_hidden(sK182,k2_relat_1(sK183)) ),
    inference(cnf_transformation,[],[f3636])).

cnf(c_1410,negated_conjecture,
    ( r2_hidden(sK182,k2_relat_1(k5_relat_1(sK184,sK183))) ),
    inference(cnf_transformation,[],[f3635])).

cnf(c_1412,negated_conjecture,
    ( v1_relat_1(sK184) ),
    inference(cnf_transformation,[],[f3633])).

cnf(c_1414,negated_conjecture,
    ( v1_relat_1(sK183) ),
    inference(cnf_transformation,[],[f3631])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65423,c_65422,c_1409,c_1410,c_1412,c_1414])).

%------------------------------------------------------------------------------
