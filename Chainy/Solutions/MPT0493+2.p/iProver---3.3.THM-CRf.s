%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0493+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:42 EST 2020

% Result     : Theorem 55.18s
% Output     : CNFRefutation 55.18s
% Verified   : 
% Statistics : Number of formulae       :   63 (  94 expanded)
%              Number of clauses        :   24 (  25 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  192 ( 305 expanded)
%              Number of equality atoms :   42 (  69 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f730,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1275,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f730])).

fof(f1715,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1275])).

fof(f1716,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1715])).

fof(f2867,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1716])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f755,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1303,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f755])).

fof(f1304,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1303])).

fof(f1305,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1306,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1304,f1305])).

fof(f1727,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1306])).

fof(f409,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f951,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f409])).

fof(f2313,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f951])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1874,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f3249,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1) ) ),
    inference(definition_unfolding,[],[f2313,f1874])).

fof(f410,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f952,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f410])).

fof(f2314,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f952])).

fof(f3250,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f2314,f1874])).

fof(f2865,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1716])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f759,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f1330,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f759])).

fof(f1331,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK17(X0,X1),X1)
          | ~ r2_hidden(sK17(X0,X1),X0) )
        & ( r2_hidden(sK17(X0,X1),X1)
          | r2_hidden(sK17(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1332,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK17(X0,X1),X1)
          | ~ r2_hidden(sK17(X0,X1),X0) )
        & ( r2_hidden(sK17(X0,X1),X1)
          | r2_hidden(sK17(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f1330,f1331])).

fof(f1767,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK17(X0,X1),X1)
      | r2_hidden(sK17(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1332])).

fof(f1768,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK17(X0,X1),X1)
      | ~ r2_hidden(sK17(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1332])).

fof(f735,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f736,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f735])).

fof(f1280,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f736])).

fof(f1281,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1280])).

fof(f1717,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK155,sK154)) != sK154
      & r1_tarski(sK154,k1_relat_1(sK155))
      & v1_relat_1(sK155) ) ),
    introduced(choice_axiom,[])).

fof(f1718,plain,
    ( k1_relat_1(k7_relat_1(sK155,sK154)) != sK154
    & r1_tarski(sK154,k1_relat_1(sK155))
    & v1_relat_1(sK155) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK154,sK155])],[f1281,f1717])).

fof(f2874,plain,(
    k1_relat_1(k7_relat_1(sK155,sK154)) != sK154 ),
    inference(cnf_transformation,[],[f1718])).

fof(f2873,plain,(
    r1_tarski(sK154,k1_relat_1(sK155)) ),
    inference(cnf_transformation,[],[f1718])).

fof(f2872,plain,(
    v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1718])).

cnf(c_1132,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2867])).

cnf(c_84358,plain,
    ( ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(X0))
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(X0,sK154)))
    | ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_180349,plain,
    ( r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(sK155))
    | ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_84358])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f1727])).

cnf(c_84431,plain,
    ( ~ r1_tarski(sK154,X0)
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),X0)
    | ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_110542,plain,
    ( ~ r1_tarski(sK154,k1_relat_1(sK155))
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(sK155))
    | ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154) ),
    inference(instantiation,[status(thm)],[c_84431])).

cnf(c_582,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3249])).

cnf(c_108015,plain,
    ( r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | k4_xboole_0(sK154,k4_xboole_0(sK154,k1_tarski(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154)))))) != k1_tarski(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154)))) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3250])).

cnf(c_84362,plain,
    ( ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | k4_xboole_0(sK154,k4_xboole_0(sK154,k1_tarski(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154)))))) = k1_tarski(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154)))) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_84378,plain,
    ( k4_xboole_0(sK154,k4_xboole_0(sK154,k1_tarski(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154)))))) = k1_tarski(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))))
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84362])).

cnf(c_1134,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2865])).

cnf(c_64364,plain,
    ( ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_64365,plain,
    ( r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154))) != iProver_top
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154) = iProver_top
    | v1_relat_1(sK155) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64364])).

cnf(c_50,plain,
    ( r2_hidden(sK17(X0,X1),X1)
    | r2_hidden(sK17(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1767])).

cnf(c_58016,plain,
    ( r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | k1_relat_1(k7_relat_1(sK155,sK154)) = sK154 ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_58017,plain,
    ( k1_relat_1(k7_relat_1(sK155,sK154)) = sK154
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154))) = iProver_top
    | r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58016])).

cnf(c_49,plain,
    ( ~ r2_hidden(sK17(X0,X1),X1)
    | ~ r2_hidden(sK17(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1768])).

cnf(c_57993,plain,
    ( ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | ~ r2_hidden(sK17(sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | k1_relat_1(k7_relat_1(sK155,sK154)) = sK154 ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_1139,negated_conjecture,
    ( k1_relat_1(k7_relat_1(sK155,sK154)) != sK154 ),
    inference(cnf_transformation,[],[f2874])).

cnf(c_1140,negated_conjecture,
    ( r1_tarski(sK154,k1_relat_1(sK155)) ),
    inference(cnf_transformation,[],[f2873])).

cnf(c_1141,negated_conjecture,
    ( v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f2872])).

cnf(c_1142,plain,
    ( v1_relat_1(sK155) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_180349,c_110542,c_108015,c_84378,c_64365,c_58017,c_57993,c_1139,c_1140,c_1142,c_1141])).

%------------------------------------------------------------------------------
