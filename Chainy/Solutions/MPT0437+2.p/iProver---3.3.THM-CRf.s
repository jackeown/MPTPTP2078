%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0437+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 14.98s
% Output     : CNFRefutation 14.98s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :  143 ( 171 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f641,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1484,plain,(
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

fof(f1485,plain,(
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
    inference(rectify,[],[f1484])).

fof(f1488,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK130(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1487,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK129(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1486,plain,(
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

fof(f1489,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK128,sK129,sK130])],[f1485,f1488,f1487,f1486])).

fof(f2507,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f3188,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f2507])).

fof(f640,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1478,plain,(
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

fof(f1479,plain,(
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
    inference(rectify,[],[f1478])).

fof(f1482,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK127(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1481,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK126(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1480,plain,(
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

fof(f1483,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK125,sK126,sK127])],[f1479,f1482,f1481,f1480])).

fof(f2503,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1483])).

fof(f3186,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2503])).

fof(f652,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f653,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k2_relat_1(X2))
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f652])).

fof(f1103,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k2_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f653])).

fof(f1104,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k2_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1103])).

fof(f1494,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k2_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & r2_hidden(k4_tarski(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK134,k2_relat_1(sK135))
        | ~ r2_hidden(sK133,k1_relat_1(sK135)) )
      & r2_hidden(k4_tarski(sK133,sK134),sK135)
      & v1_relat_1(sK135) ) ),
    introduced(choice_axiom,[])).

fof(f1495,plain,
    ( ( ~ r2_hidden(sK134,k2_relat_1(sK135))
      | ~ r2_hidden(sK133,k1_relat_1(sK135)) )
    & r2_hidden(k4_tarski(sK133,sK134),sK135)
    & v1_relat_1(sK135) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK133,sK134,sK135])],[f1104,f1494])).

fof(f2520,plain,
    ( ~ r2_hidden(sK134,k2_relat_1(sK135))
    | ~ r2_hidden(sK133,k1_relat_1(sK135)) ),
    inference(cnf_transformation,[],[f1495])).

fof(f2519,plain,(
    r2_hidden(k4_tarski(sK133,sK134),sK135) ),
    inference(cnf_transformation,[],[f1495])).

cnf(c_998,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f3188])).

cnf(c_34733,plain,
    ( ~ r2_hidden(k4_tarski(sK133,sK134),sK135)
    | r2_hidden(sK134,k2_relat_1(sK135)) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_994,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3186])).

cnf(c_34667,plain,
    ( ~ r2_hidden(k4_tarski(sK133,sK134),sK135)
    | r2_hidden(sK133,k1_relat_1(sK135)) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_1008,negated_conjecture,
    ( ~ r2_hidden(sK133,k1_relat_1(sK135))
    | ~ r2_hidden(sK134,k2_relat_1(sK135)) ),
    inference(cnf_transformation,[],[f2520])).

cnf(c_1009,negated_conjecture,
    ( r2_hidden(k4_tarski(sK133,sK134),sK135) ),
    inference(cnf_transformation,[],[f2519])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34733,c_34667,c_1008,c_1009])).

%------------------------------------------------------------------------------
