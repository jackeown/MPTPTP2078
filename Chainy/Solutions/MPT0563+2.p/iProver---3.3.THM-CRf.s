%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0563+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 27.27s
% Output     : CNFRefutation 27.27s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  163 ( 203 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1871,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f648])).

fof(f1872,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1871])).

fof(f1875,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1874,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK145(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1873,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK144(X0,X1),X3),X0)
          | ~ r2_hidden(sK144(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK144(X0,X1),X4),X0)
          | r2_hidden(sK144(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1876,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK144(X0,X1),X3),X0)
            | ~ r2_hidden(sK144(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK144(X0,X1),sK145(X0,X1)),X0)
            | r2_hidden(sK144(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK144,sK145,sK146])],[f1872,f1875,f1874,f1873])).

fof(f2971,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1876])).

fof(f3923,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2971])).

fof(f749,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1374,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f749])).

fof(f1902,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1374])).

fof(f1903,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f1902])).

fof(f1904,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK158(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK158(X0,X1,X2)),X2)
        & r2_hidden(sK158(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1905,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK158(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK158(X0,X1,X2)),X2)
            & r2_hidden(sK158(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK158])],[f1903,f1904])).

fof(f3094,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK158(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1905])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f837,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1479,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f837])).

fof(f1480,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1479])).

fof(f1481,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1482,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1480,f1481])).

fof(f1933,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1482])).

fof(f1934,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1482])).

fof(f750,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f751,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f750])).

fof(f1375,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f751])).

fof(f1906,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK160,sK159),k1_relat_1(sK160))
      & v1_relat_1(sK160) ) ),
    introduced(choice_axiom,[])).

fof(f1907,plain,
    ( ~ r1_tarski(k10_relat_1(sK160,sK159),k1_relat_1(sK160))
    & v1_relat_1(sK160) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK159,sK160])],[f1375,f1906])).

fof(f3098,plain,(
    ~ r1_tarski(k10_relat_1(sK160,sK159),k1_relat_1(sK160)) ),
    inference(cnf_transformation,[],[f1907])).

fof(f3097,plain,(
    v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f1907])).

cnf(c_1034,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3923])).

cnf(c_92669,plain,
    ( ~ r2_hidden(k4_tarski(sK11(k10_relat_1(sK160,sK159),k1_relat_1(sK160)),sK158(sK11(k10_relat_1(sK160,sK159),k1_relat_1(sK160)),sK159,sK160)),sK160)
    | r2_hidden(sK11(k10_relat_1(sK160,sK159),k1_relat_1(sK160)),k1_relat_1(sK160)) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_1157,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK158(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3094])).

cnf(c_70732,plain,
    ( r2_hidden(k4_tarski(sK11(k10_relat_1(sK160,sK159),k1_relat_1(sK160)),sK158(sK11(k10_relat_1(sK160,sK159),k1_relat_1(sK160)),sK159,sK160)),sK160)
    | ~ r2_hidden(sK11(k10_relat_1(sK160,sK159),k1_relat_1(sK160)),k10_relat_1(sK160,sK159))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1933])).

cnf(c_60486,plain,
    ( r1_tarski(k10_relat_1(sK160,sK159),k1_relat_1(sK160))
    | r2_hidden(sK11(k10_relat_1(sK160,sK159),k1_relat_1(sK160)),k10_relat_1(sK160,sK159)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1934])).

cnf(c_60478,plain,
    ( r1_tarski(k10_relat_1(sK160,sK159),k1_relat_1(sK160))
    | ~ r2_hidden(sK11(k10_relat_1(sK160,sK159),k1_relat_1(sK160)),k1_relat_1(sK160)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1159,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK160,sK159),k1_relat_1(sK160)) ),
    inference(cnf_transformation,[],[f3098])).

cnf(c_1160,negated_conjecture,
    ( v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f3097])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_92669,c_70732,c_60486,c_60478,c_1159,c_1160])).

%------------------------------------------------------------------------------
