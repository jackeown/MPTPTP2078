%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0523+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:43 EST 2020

% Result     : Theorem 38.97s
% Output     : CNFRefutation 38.97s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 116 expanded)
%              Number of clauses        :   30 (  35 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  272 ( 542 expanded)
%              Number of equality atoms :   56 (  90 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f749,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1332,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f749])).

fof(f1798,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1332])).

fof(f1799,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f1798])).

fof(f2976,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1799])).

fof(f409,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f985,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f409])).

fof(f2397,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f985])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1958,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f3376,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1) ) ),
    inference(definition_unfolding,[],[f2397,f1958])).

fof(f656,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2858,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f656])).

fof(f410,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f986,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f410])).

fof(f2398,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f986])).

fof(f3377,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f2398,f1958])).

fof(f2974,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1799])).

fof(f2975,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1799])).

fof(f655,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1219,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f655])).

fof(f1220,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1219])).

fof(f2857,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1220])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1211,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f1741,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1211])).

fof(f1742,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1741])).

fof(f1743,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1742])).

fof(f1744,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
          | ~ r2_hidden(sK130(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
            & r2_hidden(sK130(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1745,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK130(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
                    & r2_hidden(sK130(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK129,sK130])],[f1743,f1744])).

fof(f2826,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
      | ~ r2_hidden(sK130(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f2825,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f2824,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK130(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f699,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f700,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f699])).

fof(f1272,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f700])).

fof(f1785,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0))
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK151,sK152) != k5_relat_1(sK152,k6_relat_1(sK151))
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1786,plain,
    ( k8_relat_1(sK151,sK152) != k5_relat_1(sK152,k6_relat_1(sK151))
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152])],[f1272,f1785])).

fof(f2911,plain,(
    k8_relat_1(sK151,sK152) != k5_relat_1(sK152,k6_relat_1(sK151)) ),
    inference(cnf_transformation,[],[f1786])).

fof(f2910,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1786])).

cnf(c_1157,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1)))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f2976])).

cnf(c_80320,plain,
    ( ~ r2_hidden(sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),X0)
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(X0)))
    | ~ r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152)
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_121808,plain,
    ( ~ r2_hidden(sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK151)
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(sK151)))
    | ~ r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152)
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_80320])).

cnf(c_582,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3376])).

cnf(c_113620,plain,
    ( r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152)
    | k4_xboole_0(sK152,k4_xboole_0(sK152,k1_tarski(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))))))) != k1_tarski(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))))) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1041,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2858])).

cnf(c_100931,plain,
    ( v1_relat_1(k6_relat_1(sK151)) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_100932,plain,
    ( v1_relat_1(k6_relat_1(sK151)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100931])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3377])).

cnf(c_80204,plain,
    ( ~ r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152)
    | k4_xboole_0(sK152,k4_xboole_0(sK152,k1_tarski(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))))))) = k1_tarski(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))))) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_80214,plain,
    ( k4_xboole_0(sK152,k4_xboole_0(sK152,k1_tarski(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))))))) = k1_tarski(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))))
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80204])).

cnf(c_1159,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1)))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f2974])).

cnf(c_77443,plain,
    ( r2_hidden(sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK151)
    | ~ r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(sK151)))
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_1158,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k6_relat_1(X3)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2975])).

cnf(c_77440,plain,
    ( ~ r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(sK151)))
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152)
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_77441,plain,
    ( r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(sK151))) != iProver_top
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152) = iProver_top
    | v1_relat_1(sK152) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77440])).

cnf(c_1040,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2857])).

cnf(c_53048,plain,
    ( v1_relat_1(k5_relat_1(sK152,k6_relat_1(sK151)))
    | ~ v1_relat_1(k6_relat_1(sK151))
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_53049,plain,
    ( v1_relat_1(k5_relat_1(sK152,k6_relat_1(sK151))) = iProver_top
    | v1_relat_1(k6_relat_1(sK151)) != iProver_top
    | v1_relat_1(sK152) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53048])).

cnf(c_1004,plain,
    ( ~ r2_hidden(sK130(X0,X1,X2),X0)
    | ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
    | ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f2826])).

cnf(c_47013,plain,
    ( ~ r2_hidden(sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK151)
    | ~ r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(sK151)))
    | ~ r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152)
    | ~ v1_relat_1(k5_relat_1(sK152,k6_relat_1(sK151)))
    | ~ v1_relat_1(sK152)
    | k8_relat_1(sK151,sK152) = k5_relat_1(sK152,k6_relat_1(sK151)) ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_1005,plain,
    ( r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f2825])).

cnf(c_46561,plain,
    ( r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(sK151)))
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152)
    | ~ v1_relat_1(k5_relat_1(sK152,k6_relat_1(sK151)))
    | ~ v1_relat_1(sK152)
    | k8_relat_1(sK151,sK152) = k5_relat_1(sK152,k6_relat_1(sK151)) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_46562,plain,
    ( k8_relat_1(sK151,sK152) = k5_relat_1(sK152,k6_relat_1(sK151))
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(sK151))) = iProver_top
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),sK152) = iProver_top
    | v1_relat_1(k5_relat_1(sK152,k6_relat_1(sK151))) != iProver_top
    | v1_relat_1(sK152) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46561])).

cnf(c_1006,plain,
    ( r2_hidden(sK130(X0,X1,X2),X0)
    | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f2824])).

cnf(c_45443,plain,
    ( r2_hidden(sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK151)
    | r2_hidden(k4_tarski(sK129(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151))),sK130(sK151,sK152,k5_relat_1(sK152,k6_relat_1(sK151)))),k5_relat_1(sK152,k6_relat_1(sK151)))
    | ~ v1_relat_1(k5_relat_1(sK152,k6_relat_1(sK151)))
    | ~ v1_relat_1(sK152)
    | k8_relat_1(sK151,sK152) = k5_relat_1(sK152,k6_relat_1(sK151)) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_1093,negated_conjecture,
    ( k8_relat_1(sK151,sK152) != k5_relat_1(sK152,k6_relat_1(sK151)) ),
    inference(cnf_transformation,[],[f2911])).

cnf(c_1094,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2910])).

cnf(c_1185,plain,
    ( v1_relat_1(sK152) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1094])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_121808,c_113620,c_100932,c_100931,c_80214,c_77443,c_77441,c_53049,c_53048,c_47013,c_46562,c_45443,c_1093,c_1185,c_1094])).

%------------------------------------------------------------------------------
