%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0687+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 31.53s
% Output     : CNFRefutation 31.53s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 120 expanded)
%              Number of clauses        :   37 (  37 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  205 ( 312 expanded)
%              Number of equality atoms :   89 ( 141 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1586,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f775])).

fof(f2387,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1586])).

fof(f3741,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2387])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2537,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4705,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | o_0_0_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3741,f2537])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2008,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f2732,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f2008])).

fof(f3742,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2387])).

fof(f4704,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3742,f2537])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1973,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f1974,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f1973])).

fof(f2564,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1974])).

fof(f421,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2125,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f421])).

fof(f3142,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f2125])).

fof(f2731,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2008])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2663,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f4255,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2663,f2537])).

fof(f3141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f2125])).

fof(f128,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2703,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f128])).

fof(f4284,plain,(
    ! [X0] : ~ r2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2703,f2537])).

fof(f592,axiom,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3480,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f592])).

fof(f4644,plain,(
    ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f3480,f2537])).

fof(f593,axiom,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1384,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f593])).

fof(f3481,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1384])).

fof(f4645,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_setfam_1(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f3481,f2537,f2537])).

fof(f942,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f943,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f942])).

fof(f1814,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f943])).

fof(f2467,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1814])).

fof(f2468,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f2467])).

fof(f2469,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK202,k1_tarski(sK201))
        | ~ r2_hidden(sK201,k2_relat_1(sK202)) )
      & ( k1_xboole_0 != k10_relat_1(sK202,k1_tarski(sK201))
        | r2_hidden(sK201,k2_relat_1(sK202)) )
      & v1_relat_1(sK202) ) ),
    introduced(choice_axiom,[])).

fof(f2470,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK202,k1_tarski(sK201))
      | ~ r2_hidden(sK201,k2_relat_1(sK202)) )
    & ( k1_xboole_0 != k10_relat_1(sK202,k1_tarski(sK201))
      | r2_hidden(sK201,k2_relat_1(sK202)) )
    & v1_relat_1(sK202) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK201,sK202])],[f2468,f2469])).

fof(f4018,plain,
    ( k1_xboole_0 = k10_relat_1(sK202,k1_tarski(sK201))
    | ~ r2_hidden(sK201,k2_relat_1(sK202)) ),
    inference(cnf_transformation,[],[f2470])).

fof(f4773,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK202,k1_tarski(sK201))
    | ~ r2_hidden(sK201,k2_relat_1(sK202)) ),
    inference(definition_unfolding,[],[f4018,f2537])).

fof(f4017,plain,
    ( k1_xboole_0 != k10_relat_1(sK202,k1_tarski(sK201))
    | r2_hidden(sK201,k2_relat_1(sK202)) ),
    inference(cnf_transformation,[],[f2470])).

fof(f4774,plain,
    ( o_0_0_xboole_0 != k10_relat_1(sK202,k1_tarski(sK201))
    | r2_hidden(sK201,k2_relat_1(sK202)) ),
    inference(definition_unfolding,[],[f4017,f2537])).

fof(f4016,plain,(
    v1_relat_1(sK202) ),
    inference(cnf_transformation,[],[f2470])).

cnf(c_1198,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4705])).

cnf(c_115501,plain,
    ( r1_xboole_0(k2_relat_1(sK202),k1_tarski(sK201))
    | ~ v1_relat_1(sK202)
    | k10_relat_1(sK202,k1_tarski(sK201)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_200,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f2732])).

cnf(c_115462,plain,
    ( r1_xboole_0(k2_relat_1(sK202),k1_tarski(sK201))
    | k4_xboole_0(k2_relat_1(sK202),k1_tarski(sK201)) != k2_relat_1(sK202) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_1197,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4704])).

cnf(c_113580,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK202),k1_tarski(sK201))
    | ~ v1_relat_1(sK202)
    | k10_relat_1(sK202,k1_tarski(sK201)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f2564])).

cnf(c_113514,plain,
    ( ~ r1_tarski(X0,k10_relat_1(sK202,k1_tarski(sK201)))
    | r2_xboole_0(X0,k10_relat_1(sK202,k1_tarski(sK201)))
    | k10_relat_1(sK202,k1_tarski(sK201)) = X0 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_113531,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k10_relat_1(sK202,k1_tarski(sK201)))
    | r2_xboole_0(o_0_0_xboole_0,k10_relat_1(sK202,k1_tarski(sK201)))
    | k10_relat_1(sK202,k1_tarski(sK201)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_113514])).

cnf(c_599,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f3142])).

cnf(c_109100,plain,
    ( r2_hidden(sK201,k2_relat_1(sK202))
    | k4_xboole_0(k2_relat_1(sK202),k1_tarski(sK201)) = k2_relat_1(sK202) ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_109101,plain,
    ( k4_xboole_0(k2_relat_1(sK202),k1_tarski(sK201)) = k2_relat_1(sK202)
    | r2_hidden(sK201,k2_relat_1(sK202)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_109100])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f2731])).

cnf(c_109087,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK202),k1_tarski(sK201))
    | k4_xboole_0(k2_relat_1(sK202),k1_tarski(sK201)) = k2_relat_1(sK202) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_133,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4255])).

cnf(c_107982,plain,
    ( r1_tarski(o_0_0_xboole_0,k10_relat_1(sK202,k1_tarski(sK201))) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_44560,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_107065,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(o_0_0_xboole_0,k10_relat_1(sK202,k1_tarski(sK201)))
    | X1 != k10_relat_1(sK202,k1_tarski(sK201))
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_44560])).

cnf(c_107079,plain,
    ( ~ r2_xboole_0(o_0_0_xboole_0,k10_relat_1(sK202,k1_tarski(sK201)))
    | r2_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 != k10_relat_1(sK202,k1_tarski(sK201))
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_107065])).

cnf(c_600,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
    inference(cnf_transformation,[],[f3141])).

cnf(c_85143,plain,
    ( ~ r2_hidden(sK201,k2_relat_1(sK202))
    | k4_xboole_0(k2_relat_1(sK202),k1_tarski(sK201)) != k2_relat_1(sK202) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_85174,plain,
    ( k4_xboole_0(k2_relat_1(sK202),k1_tarski(sK201)) != k2_relat_1(sK202)
    | r2_hidden(sK201,k2_relat_1(sK202)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85143])).

cnf(c_44555,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_78283,plain,
    ( k10_relat_1(sK202,k1_tarski(sK201)) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k10_relat_1(sK202,k1_tarski(sK201)) ),
    inference(instantiation,[status(thm)],[c_44555])).

cnf(c_78284,plain,
    ( k10_relat_1(sK202,k1_tarski(sK201)) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k10_relat_1(sK202,k1_tarski(sK201))
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_78283])).

cnf(c_172,plain,
    ( ~ r2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4284])).

cnf(c_4846,plain,
    ( ~ r2_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_936,plain,
    ( r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4644])).

cnf(c_3382,plain,
    ( r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_937,plain,
    ( ~ r1_setfam_1(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f4645])).

cnf(c_3379,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_1472,negated_conjecture,
    ( ~ r2_hidden(sK201,k2_relat_1(sK202))
    | o_0_0_xboole_0 = k10_relat_1(sK202,k1_tarski(sK201)) ),
    inference(cnf_transformation,[],[f4773])).

cnf(c_1623,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK202,k1_tarski(sK201))
    | r2_hidden(sK201,k2_relat_1(sK202)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1472])).

cnf(c_1473,negated_conjecture,
    ( r2_hidden(sK201,k2_relat_1(sK202))
    | o_0_0_xboole_0 != k10_relat_1(sK202,k1_tarski(sK201)) ),
    inference(cnf_transformation,[],[f4774])).

cnf(c_1622,plain,
    ( o_0_0_xboole_0 != k10_relat_1(sK202,k1_tarski(sK201))
    | r2_hidden(sK201,k2_relat_1(sK202)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1473])).

cnf(c_1474,negated_conjecture,
    ( v1_relat_1(sK202) ),
    inference(cnf_transformation,[],[f4016])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_115501,c_115462,c_113580,c_113531,c_109101,c_109087,c_107982,c_107079,c_85174,c_78284,c_4846,c_3382,c_3379,c_1623,c_1622,c_1474])).

%------------------------------------------------------------------------------
