%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0662+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:49 EST 2020

% Result     : Theorem 31.78s
% Output     : CNFRefutation 31.78s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :  233 ( 348 expanded)
%              Number of equality atoms :   31 (  59 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f645,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1417,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f2214,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1417])).

fof(f2215,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2214])).

fof(f2216,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2215])).

fof(f2217,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK132(X0,X1,X2),sK133(X0,X1,X2)),X0)
          | ~ r2_hidden(sK132(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK132(X0,X1,X2),sK133(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK132(X0,X1,X2),sK133(X0,X1,X2)),X0)
            & r2_hidden(sK132(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK132(X0,X1,X2),sK133(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2218,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK132(X0,X1,X2),sK133(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK132(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK132(X0,X1,X2),sK133(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK132(X0,X1,X2),sK133(X0,X1,X2)),X0)
                    & r2_hidden(sK132(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK132(X0,X1,X2),sK133(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK132,sK133])],[f2216,f2217])).

fof(f3428,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2218])).

fof(f4772,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3428])).

fof(f908,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1729,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f908])).

fof(f1730,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1729])).

fof(f3806,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1730])).

fof(f669,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1434,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f669])).

fof(f3490,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1434])).

fof(f967,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1824,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f967])).

fof(f1825,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1824])).

fof(f2403,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1825])).

fof(f2404,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2403])).

fof(f3977,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2404])).

fof(f3978,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2404])).

fof(f4828,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f3978])).

fof(f965,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f966,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f965])).

fof(f1822,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f966])).

fof(f1823,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1822])).

fof(f2401,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK210,sK208) != k1_funct_1(k7_relat_1(sK210,sK209),sK208)
      & r2_hidden(sK208,k1_relat_1(k7_relat_1(sK210,sK209)))
      & v1_funct_1(sK210)
      & v1_relat_1(sK210) ) ),
    introduced(choice_axiom,[])).

fof(f2402,plain,
    ( k1_funct_1(sK210,sK208) != k1_funct_1(k7_relat_1(sK210,sK209),sK208)
    & r2_hidden(sK208,k1_relat_1(k7_relat_1(sK210,sK209)))
    & v1_funct_1(sK210)
    & v1_relat_1(sK210) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK208,sK209,sK210])],[f1823,f2401])).

fof(f3975,plain,(
    k1_funct_1(sK210,sK208) != k1_funct_1(k7_relat_1(sK210,sK209),sK208) ),
    inference(cnf_transformation,[],[f2402])).

fof(f3974,plain,(
    r2_hidden(sK208,k1_relat_1(k7_relat_1(sK210,sK209))) ),
    inference(cnf_transformation,[],[f2402])).

fof(f3973,plain,(
    v1_funct_1(sK210) ),
    inference(cnf_transformation,[],[f2402])).

fof(f3972,plain,(
    v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f2402])).

cnf(c_1010,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k7_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f4772])).

cnf(c_109099,plain,
    ( ~ r2_hidden(k4_tarski(sK208,k1_funct_1(k7_relat_1(sK210,sK209),sK208)),k7_relat_1(sK210,sK209))
    | r2_hidden(k4_tarski(sK208,k1_funct_1(k7_relat_1(sK210,sK209),sK208)),sK210)
    | ~ v1_relat_1(k7_relat_1(sK210,sK209))
    | ~ v1_relat_1(sK210) ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_1384,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3806])).

cnf(c_69143,plain,
    ( v1_funct_1(k7_relat_1(sK210,sK209))
    | ~ v1_funct_1(sK210)
    | ~ v1_relat_1(sK210) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_1069,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3490])).

cnf(c_67881,plain,
    ( v1_relat_1(k7_relat_1(sK210,sK209))
    | ~ v1_relat_1(sK210) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1556,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f3977])).

cnf(c_61505,plain,
    ( ~ r2_hidden(k4_tarski(sK208,k1_funct_1(k7_relat_1(sK210,sK209),sK208)),sK210)
    | ~ v1_funct_1(sK210)
    | ~ v1_relat_1(sK210)
    | k1_funct_1(sK210,sK208) = k1_funct_1(k7_relat_1(sK210,sK209),sK208) ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_1555,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4828])).

cnf(c_61502,plain,
    ( r2_hidden(k4_tarski(sK208,k1_funct_1(k7_relat_1(sK210,sK209),sK208)),k7_relat_1(sK210,sK209))
    | ~ r2_hidden(sK208,k1_relat_1(k7_relat_1(sK210,sK209)))
    | ~ v1_funct_1(k7_relat_1(sK210,sK209))
    | ~ v1_relat_1(k7_relat_1(sK210,sK209)) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_1551,negated_conjecture,
    ( k1_funct_1(sK210,sK208) != k1_funct_1(k7_relat_1(sK210,sK209),sK208) ),
    inference(cnf_transformation,[],[f3975])).

cnf(c_1552,negated_conjecture,
    ( r2_hidden(sK208,k1_relat_1(k7_relat_1(sK210,sK209))) ),
    inference(cnf_transformation,[],[f3974])).

cnf(c_1553,negated_conjecture,
    ( v1_funct_1(sK210) ),
    inference(cnf_transformation,[],[f3973])).

cnf(c_1554,negated_conjecture,
    ( v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f3972])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109099,c_69143,c_67881,c_61505,c_61502,c_1551,c_1552,c_1553,c_1554])).

%------------------------------------------------------------------------------
