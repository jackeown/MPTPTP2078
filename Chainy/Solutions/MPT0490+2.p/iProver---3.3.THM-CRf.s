%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0490+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:41 EST 2020

% Result     : Theorem 23.34s
% Output     : CNFRefutation 23.34s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 228 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f641,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1173,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f1653,plain,(
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
    inference(nnf_transformation,[],[f1173])).

fof(f1654,plain,(
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
    inference(flattening,[],[f1653])).

fof(f1655,plain,(
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
    inference(rectify,[],[f1654])).

fof(f1656,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
          | ~ r2_hidden(sK127(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
            & r2_hidden(sK127(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1657,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK127(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
                    & r2_hidden(sK127(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK127,sK128])],[f1655,f1656])).

fof(f2725,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1657])).

fof(f3561,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2725])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1183,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f2762,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1183])).

fof(f644,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1176,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f1667,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1176])).

fof(f1668,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1667])).

fof(f1669,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK134(X0,X1),sK135(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK134(X0,X1),sK135(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1670,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK134(X0,X1),sK135(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK134(X0,X1),sK135(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK134,sK135])],[f1668,f1669])).

fof(f2738,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK134(X0,X1),sK135(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1670])).

fof(f2739,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK134(X0,X1),sK135(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1670])).

fof(f732,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f733,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(negated_conjecture,[],[f732])).

fof(f1274,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k7_relat_1(X1,X0),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f733])).

fof(f1710,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(X1,X0),X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k7_relat_1(sK155,sK154),sK155)
      & v1_relat_1(sK155) ) ),
    introduced(choice_axiom,[])).

fof(f1711,plain,
    ( ~ r1_tarski(k7_relat_1(sK155,sK154),sK155)
    & v1_relat_1(sK155) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK154,sK155])],[f1274,f1710])).

fof(f2863,plain,(
    ~ r1_tarski(k7_relat_1(sK155,sK154),sK155) ),
    inference(cnf_transformation,[],[f1711])).

fof(f2862,plain,(
    v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1711])).

cnf(c_1002,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k7_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f3561])).

cnf(c_82986,plain,
    ( ~ r2_hidden(k4_tarski(sK134(k7_relat_1(sK155,sK154),sK155),sK135(k7_relat_1(sK155,sK154),sK155)),k7_relat_1(sK155,sK154))
    | r2_hidden(k4_tarski(sK134(k7_relat_1(sK155,sK154),sK155),sK135(k7_relat_1(sK155,sK154),sK155)),sK155)
    | ~ v1_relat_1(k7_relat_1(sK155,sK154))
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_1036,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2762])).

cnf(c_63735,plain,
    ( v1_relat_1(k7_relat_1(sK155,sK154))
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_1012,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK134(X0,X1),sK135(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2738])).

cnf(c_56720,plain,
    ( r1_tarski(k7_relat_1(sK155,sK154),sK155)
    | r2_hidden(k4_tarski(sK134(k7_relat_1(sK155,sK154),sK155),sK135(k7_relat_1(sK155,sK154),sK155)),k7_relat_1(sK155,sK154))
    | ~ v1_relat_1(k7_relat_1(sK155,sK154)) ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_1011,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK134(X0,X1),sK135(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2739])).

cnf(c_56689,plain,
    ( r1_tarski(k7_relat_1(sK155,sK154),sK155)
    | ~ r2_hidden(k4_tarski(sK134(k7_relat_1(sK155,sK154),sK155),sK135(k7_relat_1(sK155,sK154),sK155)),sK155)
    | ~ v1_relat_1(k7_relat_1(sK155,sK154)) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1136,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(sK155,sK154),sK155) ),
    inference(cnf_transformation,[],[f2863])).

cnf(c_1137,negated_conjecture,
    ( v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f2862])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_82986,c_63735,c_56720,c_56689,c_1136,c_1137])).

%------------------------------------------------------------------------------
