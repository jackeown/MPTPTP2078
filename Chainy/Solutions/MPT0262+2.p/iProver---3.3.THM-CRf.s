%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0262+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:31 EST 2020

% Result     : Theorem 34.71s
% Output     : CNFRefutation 34.71s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 224 expanded)
%              Number of clauses        :   39 (  71 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  138 ( 305 expanded)
%              Number of equality atoms :   65 ( 187 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f639,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f1065,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f639])).

fof(f358,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f359,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f358])).

fof(f522,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
      & ~ r2_hidden(X2,X1)
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f359])).

fof(f663,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k2_tarski(sK35,sK37),sK36)
      & ~ r2_hidden(sK37,sK36)
      & ~ r2_hidden(sK35,sK36) ) ),
    introduced(choice_axiom,[])).

fof(f664,plain,
    ( ~ r1_xboole_0(k2_tarski(sK35,sK37),sK36)
    & ~ r2_hidden(sK37,sK36)
    & ~ r2_hidden(sK35,sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37])],[f522,f663])).

fof(f1156,plain,(
    ~ r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f664])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f884,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f880,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f820,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1162,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f880,f820])).

fof(f1306,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f884,f1162])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f877,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f669,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f818,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f672,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1265,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f818,f672,f1162])).

fof(f51,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f750,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1211,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f750,f820])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f810,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1257,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f810,f672])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f878,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f1303,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f878,f672])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f834,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1276,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f834,f672])).

fof(f1157,plain,(
    ~ r2_hidden(sK37,sK36) ),
    inference(cnf_transformation,[],[f664])).

fof(f138,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f448,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f138])).

fof(f849,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f448])).

fof(f1288,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) ),
    inference(definition_unfolding,[],[f849,f1162])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f373,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f708,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f373])).

fof(f1158,plain,(
    ~ r1_xboole_0(k2_tarski(sK35,sK37),sK36) ),
    inference(cnf_transformation,[],[f664])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f976,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f1163,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f976,f1162])).

fof(f1485,plain,(
    ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK37)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37)))),sK36) ),
    inference(definition_unfolding,[],[f1158,f1163])).

cnf(c_387,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1065])).

cnf(c_14227,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_481,negated_conjecture,
    ( ~ r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f1156])).

cnf(c_14186,plain,
    ( r2_hidden(sK35,sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_107755,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35) ),
    inference(superposition,[status(thm)],[c_14227,c_14186])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1306])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f877])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f669])).

cnf(c_8499,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1265])).

cnf(c_8520,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_153,c_211,c_7])).

cnf(c_14833,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8499,c_8520])).

cnf(c_85,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1211])).

cnf(c_14396,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_25402,plain,
    ( r1_xboole_0(k4_xboole_0(X0,o_0_0_xboole_0),k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14833,c_14396])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1257])).

cnf(c_25443,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25402,c_145])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1303])).

cnf(c_18333,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1276])).

cnf(c_17468,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_18349,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_18333,c_17468])).

cnf(c_25444,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_25443,c_18349])).

cnf(c_109870,plain,
    ( r1_xboole_0(sK36,k1_tarski(sK35)) = iProver_top ),
    inference(superposition,[status(thm)],[c_107755,c_25444])).

cnf(c_480,negated_conjecture,
    ( ~ r2_hidden(sK37,sK36) ),
    inference(cnf_transformation,[],[f1157])).

cnf(c_14187,plain,
    ( r2_hidden(sK37,sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_107754,plain,
    ( k4_xboole_0(k1_tarski(sK37),sK36) = k1_tarski(sK37) ),
    inference(superposition,[status(thm)],[c_14227,c_14187])).

cnf(c_109573,plain,
    ( r1_xboole_0(sK36,k1_tarski(sK37)) = iProver_top ),
    inference(superposition,[status(thm)],[c_107754,c_25444])).

cnf(c_185,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f1288])).

cnf(c_8510,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(theory_normalisation,[status(thm)],[c_185,c_211,c_7])).

cnf(c_20427,plain,
    ( r1_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK37),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37))))))
    | ~ r1_xboole_0(sK36,k1_tarski(sK37))
    | ~ r1_xboole_0(sK36,k1_tarski(sK35)) ),
    inference(instantiation,[status(thm)],[c_8510])).

cnf(c_20428,plain,
    ( r1_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK37),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37)))))) = iProver_top
    | r1_xboole_0(sK36,k1_tarski(sK37)) != iProver_top
    | r1_xboole_0(sK36,k1_tarski(sK35)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20427])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f708])).

cnf(c_17049,plain,
    ( r1_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK37),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37))))),sK36)
    | ~ r1_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK37),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37)))))) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_17050,plain,
    ( r1_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK37),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37))))),sK36) = iProver_top
    | r1_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK37),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17049])).

cnf(c_479,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK37)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37)))),sK36) ),
    inference(cnf_transformation,[],[f1485])).

cnf(c_8365,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK37),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37))))),sK36) ),
    inference(theory_normalisation,[status(thm)],[c_479,c_211,c_7])).

cnf(c_8605,plain,
    ( r1_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK37),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37))))),sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8365])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109870,c_109573,c_20428,c_17050,c_8605])).

%------------------------------------------------------------------------------
