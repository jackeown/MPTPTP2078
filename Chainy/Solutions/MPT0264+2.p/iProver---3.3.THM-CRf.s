%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0264+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:31 EST 2020

% Result     : Theorem 15.69s
% Output     : CNFRefutation 15.69s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 177 expanded)
%              Number of clauses        :   39 (  48 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  135 ( 242 expanded)
%              Number of equality atoms :  109 ( 204 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f654,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f320])).

fof(f1100,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f654])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f672,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f360,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f361,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f360])).

fof(f525,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f361])).

fof(f666,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) )
   => ( sK35 != sK36
      & r2_hidden(sK36,sK37)
      & k3_xboole_0(k2_tarski(sK35,sK36),sK37) = k1_tarski(sK35) ) ),
    introduced(choice_axiom,[])).

fof(f667,plain,
    ( sK35 != sK36
    & r2_hidden(sK36,sK37)
    & k3_xboole_0(k2_tarski(sK35,sK36),sK37) = k1_tarski(sK35) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37])],[f525,f666])).

fof(f1161,plain,(
    k3_xboole_0(k2_tarski(sK35,sK36),sK37) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f667])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f979,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f883,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f823,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1167,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f883,f823])).

fof(f1168,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f979,f1167])).

fof(f1492,plain,(
    k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37)) = k1_tarski(sK35) ),
    inference(definition_unfolding,[],[f1161,f823,f1168])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f880,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f887,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1311,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f887,f1167])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f750,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1178,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f750,f823])).

fof(f1163,plain,(
    sK35 != sK36 ),
    inference(cnf_transformation,[],[f667])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f881,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f675,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1308,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f881,f675])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f837,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1281,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f837,f675])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f800,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1254,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f800,f823,f675,f675])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f813,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1262,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f813,f675])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f768,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f1223,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f768,f823,f823,f823])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f824,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1272,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f824,f823,f823])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f558,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f699,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f558])).

fof(f1194,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f699,f823,f675])).

fof(f355,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f521,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f355])).

fof(f1156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f521])).

fof(f1162,plain,(
    r2_hidden(sK36,sK37) ),
    inference(cnf_transformation,[],[f667])).

cnf(c_419,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f1100])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f672])).

cnf(c_483,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37)) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1492])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f880])).

cnf(c_5227,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37)) = k1_tarski(sK35) ),
    inference(theory_normalisation,[status(thm)],[c_483,c_211,c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1311])).

cnf(c_5362,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_12189,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37)) = k1_tarski(sK35) ),
    inference(demodulation,[status(thm)],[c_5227,c_5362])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1178])).

cnf(c_13920,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) ),
    inference(superposition,[status(thm)],[c_12189,c_1])).

cnf(c_13991,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) ),
    inference(superposition,[status(thm)],[c_7,c_13920])).

cnf(c_15079,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_419,c_13991])).

cnf(c_481,negated_conjecture,
    ( sK35 != sK36 ),
    inference(cnf_transformation,[],[f1163])).

cnf(c_5430,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_14793,plain,
    ( sK36 != X0
    | sK35 != X0
    | sK35 = sK36 ),
    inference(instantiation,[status(thm)],[c_5430])).

cnf(c_19685,plain,
    ( sK36 != sK35
    | sK35 = sK36
    | sK35 != sK35 ),
    inference(instantiation,[status(thm)],[c_14793])).

cnf(c_5429,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_19686,plain,
    ( sK35 = sK35 ),
    inference(instantiation,[status(thm)],[c_5429])).

cnf(c_44576,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15079,c_481,c_19685,c_19686])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1308])).

cnf(c_14059,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1281])).

cnf(c_13869,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_19437,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_14059,c_13869])).

cnf(c_44578,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) = k1_tarski(sK36) ),
    inference(demodulation,[status(thm)],[c_44576,c_19437])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1254])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1262])).

cnf(c_11094,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f1223])).

cnf(c_16336,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_11094,c_100])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1272])).

cnf(c_16356,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16336,c_145,c_155,c_11094])).

cnf(c_44615,plain,
    ( k4_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_44578,c_16356])).

cnf(c_31,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1194])).

cnf(c_18177,plain,
    ( r1_xboole_0(k1_tarski(sK36),sK37)
    | k4_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_476,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1156])).

cnf(c_13850,plain,
    ( ~ r1_xboole_0(k1_tarski(sK36),sK37)
    | ~ r2_hidden(sK36,sK37) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_482,negated_conjecture,
    ( r2_hidden(sK36,sK37) ),
    inference(cnf_transformation,[],[f1162])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44615,c_18177,c_13850,c_482])).

%------------------------------------------------------------------------------
