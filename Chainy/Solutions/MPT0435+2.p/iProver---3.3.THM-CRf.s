%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0435+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 22.21s
% Output     : CNFRefutation 22.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :  135 ( 156 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f651,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
            & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f650])).

fof(f1097,plain,(
    ? [X0,X1] :
      ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f1098,plain,(
    ? [X0,X1] :
      ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1097])).

fof(f1484,plain,
    ( ? [X0,X1] :
        ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(sK132))
      & r2_hidden(sK131,k1_relat_1(sK132))
      & v1_relat_1(sK132) ) ),
    introduced(choice_axiom,[])).

fof(f1485,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(sK132))
    & r2_hidden(sK131,k1_relat_1(sK132))
    & v1_relat_1(sK132) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK131,sK132])],[f1098,f1484])).

fof(f2508,plain,(
    ! [X2] : ~ r2_hidden(X2,k2_relat_1(sK132)) ),
    inference(cnf_transformation,[],[f1485])).

fof(f641,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1478,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f641])).

fof(f1479,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1478])).

fof(f1482,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK130(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1481,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK129(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1480,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK128(X0,X1)),X0)
          | ~ r2_hidden(sK128(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK128(X0,X1)),X0)
          | r2_hidden(sK128(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1483,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK128(X0,X1)),X0)
            | ~ r2_hidden(sK128(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK129(X0,X1),sK128(X0,X1)),X0)
            | r2_hidden(sK128(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK130(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK128,sK129,sK130])],[f1479,f1482,f1481,f1480])).

fof(f2497,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1483])).

fof(f3176,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f2497])).

fof(f640,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1472,plain,(
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
    inference(nnf_transformation,[],[f640])).

fof(f1473,plain,(
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
    inference(rectify,[],[f1472])).

fof(f1476,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK127(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1475,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK126(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1474,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK125(X0,X1),X3),X0)
          | ~ r2_hidden(sK125(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK125(X0,X1),X4),X0)
          | r2_hidden(sK125(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1477,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK125(X0,X1),X3),X0)
            | ~ r2_hidden(sK125(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK125(X0,X1),sK126(X0,X1)),X0)
            | r2_hidden(sK125(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK127(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK125,sK126,sK127])],[f1473,f1476,f1475,f1474])).

fof(f2492,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK127(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1477])).

fof(f3175,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK127(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2492])).

fof(f2507,plain,(
    r2_hidden(sK131,k1_relat_1(sK132)) ),
    inference(cnf_transformation,[],[f1485])).

cnf(c_1006,negated_conjecture,
    ( ~ r2_hidden(X0,k2_relat_1(sK132)) ),
    inference(cnf_transformation,[],[f2508])).

cnf(c_76821,plain,
    ( ~ r2_hidden(sK127(sK132,sK131),k2_relat_1(sK132)) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_998,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f3176])).

cnf(c_56559,plain,
    ( r2_hidden(sK127(sK132,sK131),k2_relat_1(sK132))
    | ~ r2_hidden(k4_tarski(sK131,sK127(sK132,sK131)),sK132) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_995,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK127(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f3175])).

cnf(c_51296,plain,
    ( r2_hidden(k4_tarski(sK131,sK127(sK132,sK131)),sK132)
    | ~ r2_hidden(sK131,k1_relat_1(sK132)) ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_1007,negated_conjecture,
    ( r2_hidden(sK131,k1_relat_1(sK132)) ),
    inference(cnf_transformation,[],[f2507])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76821,c_56559,c_51296,c_1007])).

%------------------------------------------------------------------------------
