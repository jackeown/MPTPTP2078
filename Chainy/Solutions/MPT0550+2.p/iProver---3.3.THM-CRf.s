%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0550+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 31.49s
% Output     : CNFRefutation 31.49s
% Verified   : 
% Statistics : Number of formulae       :   54 (  78 expanded)
%              Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 233 expanded)
%              Number of equality atoms :   58 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f734,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f735,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f734])).

fof(f1341,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f735])).

fof(f1342,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1341])).

fof(f1864,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK156,sK155)
      & r1_tarski(sK155,k1_relat_1(sK156))
      & k1_xboole_0 != sK155
      & v1_relat_1(sK156) ) ),
    introduced(choice_axiom,[])).

fof(f1865,plain,
    ( k1_xboole_0 = k9_relat_1(sK156,sK155)
    & r1_tarski(sK155,k1_relat_1(sK156))
    & k1_xboole_0 != sK155
    & v1_relat_1(sK156) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK155,sK156])],[f1342,f1864])).

fof(f3035,plain,(
    k1_xboole_0 = k9_relat_1(sK156,sK155) ),
    inference(cnf_transformation,[],[f1865])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1889,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3650,plain,(
    o_0_0_xboole_0 = k9_relat_1(sK156,sK155) ),
    inference(definition_unfolding,[],[f3035,f1889])).

fof(f733,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1340,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f733])).

fof(f1863,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1340])).

fof(f3030,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1863])).

fof(f3649,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | o_0_0_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3030,f1889])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f824,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f1925,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f824])).

fof(f133,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f892,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f133])).

fof(f893,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f892])).

fof(f2061,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f893])).

fof(f3247,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f2061,f1889])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1488,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f1489,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1488])).

fof(f1948,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f3692,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1948])).

fof(f3034,plain,(
    r1_tarski(sK155,k1_relat_1(sK156)) ),
    inference(cnf_transformation,[],[f1865])).

fof(f3033,plain,(
    k1_xboole_0 != sK155 ),
    inference(cnf_transformation,[],[f1865])).

fof(f3651,plain,(
    o_0_0_xboole_0 != sK155 ),
    inference(definition_unfolding,[],[f3033,f1889])).

fof(f3032,plain,(
    v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f1865])).

cnf(c_1136,negated_conjecture,
    ( o_0_0_xboole_0 = k9_relat_1(sK156,sK155) ),
    inference(cnf_transformation,[],[f3650])).

cnf(c_1135,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3649])).

cnf(c_33361,plain,
    ( k9_relat_1(X0,X1) != o_0_0_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1135])).

cnf(c_121102,plain,
    ( r1_xboole_0(k1_relat_1(sK156),sK155) = iProver_top
    | v1_relat_1(sK156) != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_33361])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1925])).

cnf(c_70464,plain,
    ( r1_xboole_0(X0,k1_relat_1(sK156))
    | ~ r1_xboole_0(k1_relat_1(sK156),X0) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_115259,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
    | r1_xboole_0(sK155,k1_relat_1(sK156)) ),
    inference(instantiation,[status(thm)],[c_70464])).

cnf(c_115260,plain,
    ( r1_xboole_0(k1_relat_1(sK156),sK155) != iProver_top
    | r1_xboole_0(sK155,k1_relat_1(sK156)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115259])).

cnf(c_178,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f3247])).

cnf(c_45315,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(sK155,X0)
    | ~ r1_tarski(sK155,X1)
    | o_0_0_xboole_0 = sK155 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_57577,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK156))
    | ~ r1_tarski(sK155,X0)
    | ~ r1_tarski(sK155,k1_relat_1(sK156))
    | o_0_0_xboole_0 = sK155 ),
    inference(instantiation,[status(thm)],[c_45315])).

cnf(c_84812,plain,
    ( ~ r1_xboole_0(sK155,k1_relat_1(sK156))
    | ~ r1_tarski(sK155,k1_relat_1(sK156))
    | ~ r1_tarski(sK155,sK155)
    | o_0_0_xboole_0 = sK155 ),
    inference(instantiation,[status(thm)],[c_57577])).

cnf(c_84813,plain,
    ( o_0_0_xboole_0 = sK155
    | r1_xboole_0(sK155,k1_relat_1(sK156)) != iProver_top
    | r1_tarski(sK155,k1_relat_1(sK156)) != iProver_top
    | r1_tarski(sK155,sK155) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84812])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3692])).

cnf(c_56009,plain,
    ( r1_tarski(sK155,sK155) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_56012,plain,
    ( r1_tarski(sK155,sK155) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56009])).

cnf(c_1137,negated_conjecture,
    ( r1_tarski(sK155,k1_relat_1(sK156)) ),
    inference(cnf_transformation,[],[f3034])).

cnf(c_1229,plain,
    ( r1_tarski(sK155,k1_relat_1(sK156)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_1138,negated_conjecture,
    ( o_0_0_xboole_0 != sK155 ),
    inference(cnf_transformation,[],[f3651])).

cnf(c_1139,negated_conjecture,
    ( v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f3032])).

cnf(c_1228,plain,
    ( v1_relat_1(sK156) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_121102,c_115260,c_84813,c_56012,c_1229,c_1138,c_1228])).

%------------------------------------------------------------------------------
