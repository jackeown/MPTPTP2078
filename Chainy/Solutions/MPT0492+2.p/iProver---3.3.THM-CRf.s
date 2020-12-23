%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0492+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:42 EST 2020

% Result     : Theorem 54.30s
% Output     : CNFRefutation 54.30s
% Verified   : 
% Statistics : Number of formulae       :   45 (  76 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 ( 394 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f730,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1274,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f730])).

fof(f1712,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1274])).

fof(f1713,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1712])).

fof(f2864,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1713])).

fof(f2863,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1713])).

fof(f2862,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1713])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1309,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f1310,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f1309])).

fof(f1311,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1310])).

fof(f1312,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
          | ~ r2_hidden(sK13(X0,X1,X2),X0)
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(sK13(X0,X1,X2),X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1313,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
            | ~ r2_hidden(sK13(X0,X1,X2),X0)
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK13(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f1311,f1312])).

fof(f1738,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f1313])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1871,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f2893,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f1738,f1871])).

fof(f1736,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f1313])).

fof(f2895,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f1736,f1871])).

fof(f1737,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f1313])).

fof(f2894,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f1737,f1871])).

fof(f734,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f735,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(negated_conjecture,[],[f734])).

fof(f1278,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f735])).

fof(f1714,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( k3_xboole_0(k1_relat_1(sK155),sK154) != k1_relat_1(k7_relat_1(sK155,sK154))
      & v1_relat_1(sK155) ) ),
    introduced(choice_axiom,[])).

fof(f1715,plain,
    ( k3_xboole_0(k1_relat_1(sK155),sK154) != k1_relat_1(k7_relat_1(sK155,sK154))
    & v1_relat_1(sK155) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK154,sK155])],[f1278,f1714])).

fof(f2869,plain,(
    k3_xboole_0(k1_relat_1(sK155),sK154) != k1_relat_1(k7_relat_1(sK155,sK154)) ),
    inference(cnf_transformation,[],[f1715])).

fof(f3402,plain,(
    k4_xboole_0(k1_relat_1(sK155),k4_xboole_0(k1_relat_1(sK155),sK154)) != k1_relat_1(k7_relat_1(sK155,sK154)) ),
    inference(definition_unfolding,[],[f2869,f1871])).

fof(f2868,plain,(
    v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1715])).

cnf(c_1132,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2864])).

cnf(c_79406,plain,
    ( ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(X0))
    | r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(X0,sK154)))
    | ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_158328,plain,
    ( r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(sK155))
    | ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_79406])).

cnf(c_1133,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f2863])).

cnf(c_65026,plain,
    ( ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(sK155))
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_1134,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2862])).

cnf(c_65023,plain,
    ( ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | ~ v1_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_19,plain,
    ( ~ r2_hidden(sK13(X0,X1,X2),X1)
    | ~ r2_hidden(sK13(X0,X1,X2),X0)
    | ~ r2_hidden(sK13(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f2893])).

cnf(c_60866,plain,
    ( ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(sK155))
    | ~ r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | k4_xboole_0(k1_relat_1(sK155),k4_xboole_0(k1_relat_1(sK155),sK154)) = k1_relat_1(k7_relat_1(sK155,sK154)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( r2_hidden(sK13(X0,X1,X2),X0)
    | r2_hidden(sK13(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f2895])).

cnf(c_59511,plain,
    ( r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(sK155))
    | k4_xboole_0(k1_relat_1(sK155),k4_xboole_0(k1_relat_1(sK155),sK154)) = k1_relat_1(k7_relat_1(sK155,sK154)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( r2_hidden(sK13(X0,X1,X2),X1)
    | r2_hidden(sK13(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f2894])).

cnf(c_59452,plain,
    ( r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),k1_relat_1(k7_relat_1(sK155,sK154)))
    | r2_hidden(sK13(k1_relat_1(sK155),sK154,k1_relat_1(k7_relat_1(sK155,sK154))),sK154)
    | k4_xboole_0(k1_relat_1(sK155),k4_xboole_0(k1_relat_1(sK155),sK154)) = k1_relat_1(k7_relat_1(sK155,sK154)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1138,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(sK155),k4_xboole_0(k1_relat_1(sK155),sK154)) != k1_relat_1(k7_relat_1(sK155,sK154)) ),
    inference(cnf_transformation,[],[f3402])).

cnf(c_1139,negated_conjecture,
    ( v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f2868])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_158328,c_65026,c_65023,c_60866,c_59511,c_59452,c_1138,c_1139])).

%------------------------------------------------------------------------------
