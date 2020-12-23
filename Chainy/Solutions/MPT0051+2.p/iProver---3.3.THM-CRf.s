%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0051+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:15 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 107 expanded)
%              Number of clauses        :   33 (  37 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 135 expanded)
%              Number of equality atoms :   69 (  94 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f301,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f211,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f350,plain,(
    ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f301,f211,f211])).

fof(f81,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
       => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f81])).

fof(f144,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f82])).

fof(f202,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(sK15,k2_xboole_0(sK16,sK17))
      & r1_tarski(k4_xboole_0(sK15,sK16),sK17) ) ),
    introduced(choice_axiom,[])).

fof(f203,plain,
    ( ~ r1_tarski(sK15,k2_xboole_0(sK16,sK17))
    & r1_tarski(k4_xboole_0(sK15,sK16),sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f144,f202])).

fof(f320,plain,(
    r1_tarski(k4_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f203])).

fof(f65,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f135,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f303,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f47,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f283,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f207,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f84,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f323,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f84])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f206,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f240,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f94])).

fof(f56,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f294,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f54,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f292,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f54])).

fof(f77,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f316,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f77])).

fof(f51,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f287,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

fof(f349,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f287,f211])).

fof(f83,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f322,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f83])).

fof(f357,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f322,f211,f211])).

fof(f78,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f317,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f78])).

fof(f72,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f201,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f310,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f201])).

fof(f353,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f310,f211])).

fof(f321,plain,(
    ~ r1_tarski(sK15,k2_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f203])).

cnf(c_95,plain,
    ( k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f350])).

cnf(c_115,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f320])).

cnf(c_3777,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK16),sK17) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_97,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(k2_xboole_0(X0,X2),X1) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f303])).

cnf(c_77,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f283])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f207])).

cnf(c_117,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f323])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f206])).

cnf(c_2010,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X1,k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_97,c_77,c_3,c_117,c_2])).

cnf(c_3787,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X0,X2))
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2010])).

cnf(c_48976,plain,
    ( k3_xboole_0(sK17,k2_xboole_0(k4_xboole_0(sK15,sK16),X0)) = k2_xboole_0(k4_xboole_0(sK15,sK16),k3_xboole_0(sK17,X0)) ),
    inference(superposition,[status(thm)],[c_3777,c_3787])).

cnf(c_34,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f240])).

cnf(c_88,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f294])).

cnf(c_6699,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_34,c_88])).

cnf(c_86,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f292])).

cnf(c_4599,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_86])).

cnf(c_6756,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6699,c_4599])).

cnf(c_110,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f316])).

cnf(c_7606,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_6756,c_110])).

cnf(c_81,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f349])).

cnf(c_4577,plain,
    ( k2_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_81,c_2])).

cnf(c_4681,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_4577,c_110])).

cnf(c_116,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f357])).

cnf(c_4690,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4681,c_116])).

cnf(c_7623,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7606,c_4690])).

cnf(c_51578,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK15,sK16),k3_xboole_0(sK17,X0)),sK17) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_48976,c_7623])).

cnf(c_51997,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK15,sK16),o_0_0_xboole_0),sK17) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_95,c_51578])).

cnf(c_111,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f317])).

cnf(c_52137,plain,
    ( k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51997,c_81,c_111])).

cnf(c_105,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f353])).

cnf(c_4541,plain,
    ( r1_tarski(sK15,k2_xboole_0(sK16,sK17))
    | k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_114,negated_conjecture,
    ( ~ r1_tarski(sK15,k2_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f321])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52137,c_4541,c_114])).

%------------------------------------------------------------------------------
