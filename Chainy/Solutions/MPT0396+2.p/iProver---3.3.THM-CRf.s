%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0396+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 22.88s
% Output     : CNFRefutation 22.88s
% Verified   : 
% Statistics : Number of formulae       :   45 (  59 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 162 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f804,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f441])).

fof(f1906,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f804])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f625,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f626,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f625])).

fof(f1381,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f626])).

fof(f545,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f581,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f545])).

fof(f923,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f581])).

fof(f1251,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK94(X1,X2))
        & r2_hidden(sK94(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1252,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK94(X1,X2))
            & r2_hidden(sK94(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK94])],[f923,f1251])).

fof(f2129,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK94(X1,X2),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1252])).

fof(f2130,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK94(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1252])).

fof(f443,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f805,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f443])).

fof(f1150,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK65(X0,X1),X1)
        & r2_hidden(sK65(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1151,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK65(X0,X1),X1)
        & r2_hidden(sK65(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK65])],[f805,f1150])).

fof(f1908,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK65(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1151])).

fof(f1909,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK65(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1151])).

fof(f555,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f556,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f555])).

fof(f927,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f556])).

fof(f1257,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK97),k3_tarski(sK98))
      & r1_setfam_1(sK97,sK98) ) ),
    introduced(choice_axiom,[])).

fof(f1258,plain,
    ( ~ r1_tarski(k3_tarski(sK97),k3_tarski(sK98))
    & r1_setfam_1(sK97,sK98) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK97,sK98])],[f927,f1257])).

fof(f2142,plain,(
    ~ r1_tarski(k3_tarski(sK97),k3_tarski(sK98)) ),
    inference(cnf_transformation,[],[f1258])).

fof(f2141,plain,(
    r1_setfam_1(sK97,sK98) ),
    inference(cnf_transformation,[],[f1258])).

cnf(c_632,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1906])).

cnf(c_93305,plain,
    ( r1_tarski(sK94(sK98,sK65(sK97,k3_tarski(sK98))),k3_tarski(sK98))
    | ~ r2_hidden(sK94(sK98,sK65(sK97,k3_tarski(sK98))),sK98) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1381])).

cnf(c_50025,plain,
    ( ~ r1_tarski(X0,k3_tarski(sK98))
    | ~ r1_tarski(sK65(sK97,k3_tarski(sK98)),X0)
    | r1_tarski(sK65(sK97,k3_tarski(sK98)),k3_tarski(sK98)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_93255,plain,
    ( ~ r1_tarski(sK94(sK98,sK65(sK97,k3_tarski(sK98))),k3_tarski(sK98))
    | ~ r1_tarski(sK65(sK97,k3_tarski(sK98)),sK94(sK98,sK65(sK97,k3_tarski(sK98))))
    | r1_tarski(sK65(sK97,k3_tarski(sK98)),k3_tarski(sK98)) ),
    inference(instantiation,[status(thm)],[c_50025])).

cnf(c_854,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK94(X1,X2),X1) ),
    inference(cnf_transformation,[],[f2129])).

cnf(c_50155,plain,
    ( ~ r1_setfam_1(sK97,X0)
    | r2_hidden(sK94(X0,sK65(sK97,k3_tarski(sK98))),X0)
    | ~ r2_hidden(sK65(sK97,k3_tarski(sK98)),sK97) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_81396,plain,
    ( ~ r1_setfam_1(sK97,sK98)
    | r2_hidden(sK94(sK98,sK65(sK97,k3_tarski(sK98))),sK98)
    | ~ r2_hidden(sK65(sK97,k3_tarski(sK98)),sK97) ),
    inference(instantiation,[status(thm)],[c_50155])).

cnf(c_853,plain,
    ( ~ r1_setfam_1(X0,X1)
    | r1_tarski(X2,sK94(X1,X2))
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f2130])).

cnf(c_50156,plain,
    ( ~ r1_setfam_1(sK97,X0)
    | r1_tarski(sK65(sK97,k3_tarski(sK98)),sK94(X0,sK65(sK97,k3_tarski(sK98))))
    | ~ r2_hidden(sK65(sK97,k3_tarski(sK98)),sK97) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_75568,plain,
    ( ~ r1_setfam_1(sK97,sK98)
    | r1_tarski(sK65(sK97,k3_tarski(sK98)),sK94(sK98,sK65(sK97,k3_tarski(sK98))))
    | ~ r2_hidden(sK65(sK97,k3_tarski(sK98)),sK97) ),
    inference(instantiation,[status(thm)],[c_50156])).

cnf(c_635,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | r2_hidden(sK65(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1908])).

cnf(c_43893,plain,
    ( r1_tarski(k3_tarski(sK97),k3_tarski(sK98))
    | r2_hidden(sK65(sK97,k3_tarski(sK98)),sK97) ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_634,plain,
    ( ~ r1_tarski(sK65(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f1909])).

cnf(c_43890,plain,
    ( ~ r1_tarski(sK65(sK97,k3_tarski(sK98)),k3_tarski(sK98))
    | r1_tarski(k3_tarski(sK97),k3_tarski(sK98)) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_865,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(sK97),k3_tarski(sK98)) ),
    inference(cnf_transformation,[],[f2142])).

cnf(c_866,negated_conjecture,
    ( r1_setfam_1(sK97,sK98) ),
    inference(cnf_transformation,[],[f2141])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93305,c_93255,c_81396,c_75568,c_43893,c_43890,c_865,c_866])).

%------------------------------------------------------------------------------
