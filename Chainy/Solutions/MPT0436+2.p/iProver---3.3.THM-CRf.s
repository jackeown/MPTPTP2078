%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0436+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 21.75s
% Output     : CNFRefutation 21.75s
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
fof(f651,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f652,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
            & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f651])).

fof(f1100,plain,(
    ? [X0,X1] :
      ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
      & r2_hidden(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f1101,plain,(
    ? [X0,X1] :
      ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
      & r2_hidden(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1100])).

fof(f1489,plain,
    ( ? [X0,X1] :
        ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
        & r2_hidden(X0,k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(sK133))
      & r2_hidden(sK132,k2_relat_1(sK133))
      & v1_relat_1(sK133) ) ),
    introduced(choice_axiom,[])).

fof(f1490,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(sK133))
    & r2_hidden(sK132,k2_relat_1(sK133))
    & v1_relat_1(sK133) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK132,sK133])],[f1101,f1489])).

fof(f2514,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_relat_1(sK133)) ),
    inference(cnf_transformation,[],[f1490])).

fof(f640,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1475,plain,(
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

fof(f1476,plain,(
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
    inference(rectify,[],[f1475])).

fof(f1479,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK127(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1478,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK126(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1477,plain,(
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

fof(f1480,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK125,sK126,sK127])],[f1476,f1479,f1478,f1477])).

fof(f2498,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1480])).

fof(f3180,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2498])).

fof(f641,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1481,plain,(
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

fof(f1482,plain,(
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
    inference(rectify,[],[f1481])).

fof(f1485,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK130(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1484,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK129(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1483,plain,(
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

fof(f1486,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK128,sK129,sK130])],[f1482,f1485,f1484,f1483])).

fof(f2501,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK130(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1486])).

fof(f3183,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK130(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2501])).

fof(f2513,plain,(
    r2_hidden(sK132,k2_relat_1(sK133)) ),
    inference(cnf_transformation,[],[f1490])).

cnf(c_1007,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK133)) ),
    inference(cnf_transformation,[],[f2514])).

cnf(c_76989,plain,
    ( ~ r2_hidden(sK130(sK133,sK132),k1_relat_1(sK133)) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_994,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3180])).

cnf(c_56668,plain,
    ( r2_hidden(sK130(sK133,sK132),k1_relat_1(sK133))
    | ~ r2_hidden(k4_tarski(sK130(sK133,sK132),sK132),sK133) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_999,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK130(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f3183])).

cnf(c_51308,plain,
    ( r2_hidden(k4_tarski(sK130(sK133,sK132),sK132),sK133)
    | ~ r2_hidden(sK132,k2_relat_1(sK133)) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_1008,negated_conjecture,
    ( r2_hidden(sK132,k2_relat_1(sK133)) ),
    inference(cnf_transformation,[],[f2513])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76989,c_56668,c_51308,c_1008])).

%------------------------------------------------------------------------------
