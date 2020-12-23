%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0095+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:20 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 119 expanded)
%              Number of clauses        :   30 (  37 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 139 expanded)
%              Number of equality atoms :   72 ( 119 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f296,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f417,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f473,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f296,f417,f417])).

fof(f92,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f422,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

fof(f532,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f422,f417])).

fof(f90,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f420,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f90])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f295,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f85,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f415,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f300,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f527,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f415,f300])).

fof(f134,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f135,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
       => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(negated_conjecture,[],[f134])).

fof(f232,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f291,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0
        & r1_xboole_0(X0,X1) )
   => ( k4_xboole_0(k2_xboole_0(sK15,sK16),sK16) != sK15
      & r1_xboole_0(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f292,plain,
    ( k4_xboole_0(k2_xboole_0(sK15,sK16),sK16) != sK15
    & r1_xboole_0(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f232,f291])).

fof(f468,plain,(
    r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f292])).

fof(f133,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f231,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f133])).

fof(f467,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f231])).

fof(f65,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f394,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

fof(f518,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f394,f417,f300,f300])).

fof(f77,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f407,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f77])).

fof(f525,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f407,f300])).

fof(f93,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f423,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

fof(f533,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f423,f417])).

fof(f76,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f406,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f53,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f380,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f505,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f380,f300])).

fof(f79,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f409,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f79])).

fof(f469,plain,(
    k4_xboole_0(k2_xboole_0(sK15,sK16),sK16) != sK15 ),
    inference(cnf_transformation,[],[f292])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f473])).

cnf(c_126,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f532])).

cnf(c_124,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f420])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f295])).

cnf(c_2809,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_126,c_124,c_2])).

cnf(c_120,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f527])).

cnf(c_6541,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2809,c_120])).

cnf(c_6811,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_6541])).

cnf(c_173,negated_conjecture,
    ( r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f468])).

cnf(c_5291,plain,
    ( r1_xboole_0(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_171,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f467])).

cnf(c_2803,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X1,X2),X0) = k2_xboole_0(X1,k4_xboole_0(X2,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_171,c_124,c_2])).

cnf(c_5292,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2803])).

cnf(c_14912,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,X0),sK15) = k2_xboole_0(sK16,k4_xboole_0(X0,sK15)) ),
    inference(superposition,[status(thm)],[c_5291,c_5292])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f518])).

cnf(c_112,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f525])).

cnf(c_5454,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_99,c_112])).

cnf(c_127,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f533])).

cnf(c_9491,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,o_0_0_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5454,c_127])).

cnf(c_111,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f406])).

cnf(c_6543,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_2809,c_111])).

cnf(c_9597,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9491,c_112,c_6543])).

cnf(c_16103,plain,
    ( k4_xboole_0(sK15,k2_xboole_0(sK16,k4_xboole_0(X0,sK15))) = sK15 ),
    inference(superposition,[status(thm)],[c_14912,c_9597])).

cnf(c_16637,plain,
    ( k4_xboole_0(sK15,k2_xboole_0(sK16,o_0_0_xboole_0)) = sK15 ),
    inference(superposition,[status(thm)],[c_6811,c_16103])).

cnf(c_85,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f505])).

cnf(c_16735,plain,
    ( k4_xboole_0(sK15,sK16) = sK15 ),
    inference(demodulation,[status(thm)],[c_16637,c_85])).

cnf(c_114,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f409])).

cnf(c_172,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(sK15,sK16),sK16) != sK15 ),
    inference(cnf_transformation,[],[f469])).

cnf(c_5471,plain,
    ( k4_xboole_0(sK15,sK16) != sK15 ),
    inference(demodulation,[status(thm)],[c_114,c_172])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16735,c_5471])).

%------------------------------------------------------------------------------
