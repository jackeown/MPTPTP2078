%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0496+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:42 EST 2020

% Result     : Timeout 59.47s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  231 ( 463 expanded)
%              Number of equality atoms :   27 (  53 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f721,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1267,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f1717,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1267])).

fof(f1718,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f1717])).

fof(f2859,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1718])).

fof(f655,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2774,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f655])).

fof(f2857,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1718])).

fof(f2858,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1718])).

fof(f654,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1187,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f654])).

fof(f1188,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1187])).

fof(f2773,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1188])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1179,plain,(
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

fof(f1666,plain,(
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
    inference(nnf_transformation,[],[f1179])).

fof(f1667,plain,(
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
    inference(flattening,[],[f1666])).

fof(f1668,plain,(
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
    inference(rectify,[],[f1667])).

fof(f1669,plain,(
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

fof(f1670,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK127,sK128])],[f1668,f1669])).

fof(f2742,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
      | ~ r2_hidden(sK127(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1670])).

fof(f2741,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1670])).

fof(f2740,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK127(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1670])).

fof(f738,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f739,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(negated_conjecture,[],[f738])).

fof(f1287,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f739])).

fof(f1723,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK155,sK154) != k5_relat_1(k6_relat_1(sK154),sK155)
      & v1_relat_1(sK155) ) ),
    introduced(choice_axiom,[])).

fof(f1724,plain,
    ( k7_relat_1(sK155,sK154) != k5_relat_1(k6_relat_1(sK154),sK155)
    & v1_relat_1(sK155) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK154,sK155])],[f1287,f1723])).

fof(f2882,plain,(
    k7_relat_1(sK155,sK154) != k5_relat_1(k6_relat_1(sK154),sK155) ),
    inference(cnf_transformation,[],[f1724])).

fof(f2881,plain,(
    v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1724])).

cnf(c_1118,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f2859])).

cnf(c_83233,plain,
    ( ~ r2_hidden(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK154)
    | ~ r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),X0),X1)
    | r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),X0),k5_relat_1(k6_relat_1(sK154),X1))
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_189898,plain,
    ( ~ r2_hidden(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK154)
    | r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),k5_relat_1(k6_relat_1(sK154),sK155))
    | ~ r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),sK155)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_83233])).

cnf(c_1035,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2774])).

cnf(c_87284,plain,
    ( v1_relat_1(k6_relat_1(sK154)) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_1120,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f2857])).

cnf(c_74289,plain,
    ( r2_hidden(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK154)
    | ~ r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),k5_relat_1(k6_relat_1(sK154),sK155))
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_1119,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2858])).

cnf(c_74286,plain,
    ( ~ r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),k5_relat_1(k6_relat_1(sK154),sK155))
    | r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),sK155)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_1034,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2773])).

cnf(c_51665,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK154),sK155))
    | ~ v1_relat_1(k6_relat_1(sK154))
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_998,plain,
    ( ~ r2_hidden(sK127(X0,X1,X2),X1)
    | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
    | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f2742])).

cnf(c_45681,plain,
    ( ~ r2_hidden(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK154)
    | ~ r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),k5_relat_1(k6_relat_1(sK154),sK155))
    | ~ r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),sK155)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK154),sK155))
    | ~ v1_relat_1(sK155)
    | k7_relat_1(sK155,sK154) = k5_relat_1(k6_relat_1(sK154),sK155) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_999,plain,
    ( r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f2741])).

cnf(c_45441,plain,
    ( r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),k5_relat_1(k6_relat_1(sK154),sK155))
    | r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),sK155)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK154),sK155))
    | ~ v1_relat_1(sK155)
    | k7_relat_1(sK155,sK154) = k5_relat_1(k6_relat_1(sK154),sK155) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_1000,plain,
    ( r2_hidden(sK127(X0,X1,X2),X1)
    | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f2740])).

cnf(c_44281,plain,
    ( r2_hidden(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK154)
    | r2_hidden(k4_tarski(sK127(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155)),sK128(sK155,sK154,k5_relat_1(k6_relat_1(sK154),sK155))),k5_relat_1(k6_relat_1(sK154),sK155))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK154),sK155))
    | ~ v1_relat_1(sK155)
    | k7_relat_1(sK155,sK154) = k5_relat_1(k6_relat_1(sK154),sK155) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_1142,negated_conjecture,
    ( k7_relat_1(sK155,sK154) != k5_relat_1(k6_relat_1(sK154),sK155) ),
    inference(cnf_transformation,[],[f2882])).

cnf(c_1143,negated_conjecture,
    ( v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f2881])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_189898,c_87284,c_74289,c_74286,c_51665,c_45681,c_45441,c_44281,c_1142,c_1143])).

%------------------------------------------------------------------------------
