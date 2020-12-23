%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0079+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:18 EST 2020

% Result     : Theorem 31.46s
% Output     : CNFRefutation 31.46s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 827 expanded)
%              Number of clauses        :   90 ( 246 expanded)
%              Number of leaves         :   26 ( 239 expanded)
%              Depth                    :   20
%              Number of atoms          :  220 (1167 expanded)
%              Number of equality atoms :  174 ( 937 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f117,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f116])).

fof(f199,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f117])).

fof(f200,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f199])).

fof(f259,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK16 != sK17
      & r1_xboole_0(sK18,sK16)
      & r1_xboole_0(sK17,sK15)
      & k2_xboole_0(sK15,sK16) = k2_xboole_0(sK17,sK18) ) ),
    introduced(choice_axiom,[])).

fof(f260,plain,
    ( sK16 != sK17
    & r1_xboole_0(sK18,sK16)
    & r1_xboole_0(sK17,sK15)
    & k2_xboole_0(sK15,sK16) = k2_xboole_0(sK17,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18])],[f200,f259])).

fof(f418,plain,(
    r1_xboole_0(sK17,sK15) ),
    inference(cnf_transformation,[],[f260])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f229,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f291,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f229])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f385,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f268,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f435,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f291,f385,f268])).

fof(f417,plain,(
    k2_xboole_0(sK15,sK16) = k2_xboole_0(sK17,sK18) ),
    inference(cnf_transformation,[],[f260])).

fof(f90,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f388,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f90])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f263,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f85,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f383,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

fof(f480,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f383,f268])).

fof(f59,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f356,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f465,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f356,f385,f385])).

fof(f81,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f379,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f81])).

fof(f89,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f387,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f483,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f387,f268,f268])).

fof(f53,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f348,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f458,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f348,f268])).

fof(f96,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f394,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

fof(f489,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f394,f385])).

fof(f77,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f375,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f77])).

fof(f478,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f375,f268])).

fof(f65,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f362,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

fof(f471,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f362,f385,f268,f268])).

fof(f419,plain,(
    r1_xboole_0(sK18,sK16) ),
    inference(cnf_transformation,[],[f260])).

fof(f113,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f412,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f113])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f264,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f426,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f264,f385,f385])).

fof(f76,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f374,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f80,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f378,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f80])).

fof(f88,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f386,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f88])).

fof(f482,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f386,f385,f385])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f123,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f298,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f123])).

fof(f79,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f377,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f79])).

fof(f92,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f390,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

fof(f485,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f390,f385])).

fof(f86,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f384,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f481,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f384,f385])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f251,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f251])).

fof(f329,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f252])).

fof(f327,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f252])).

fof(f508,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f327])).

fof(f420,plain,(
    sK16 != sK17 ),
    inference(cnf_transformation,[],[f260])).

cnf(c_155,negated_conjecture,
    ( r1_xboole_0(sK17,sK15) ),
    inference(cnf_transformation,[],[f418])).

cnf(c_4549,plain,
    ( r1_xboole_0(sK17,sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_29,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f435])).

cnf(c_4632,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = o_0_0_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_116748,plain,
    ( k4_xboole_0(sK17,k4_xboole_0(sK17,sK15)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_4549,c_4632])).

cnf(c_156,negated_conjecture,
    ( k2_xboole_0(sK15,sK16) = k2_xboole_0(sK17,sK18) ),
    inference(cnf_transformation,[],[f417])).

cnf(c_124,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f388])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f263])).

cnf(c_2468,negated_conjecture,
    ( k2_xboole_0(sK16,sK15) = k2_xboole_0(sK17,sK18) ),
    inference(theory_normalisation,[status(thm)],[c_156,c_124,c_2])).

cnf(c_120,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f480])).

cnf(c_6707,plain,
    ( k4_xboole_0(sK17,k2_xboole_0(sK16,sK15)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2468,c_120])).

cnf(c_93,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f465])).

cnf(c_116,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f379])).

cnf(c_12316,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(o_0_0_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_120,c_116])).

cnf(c_123,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f483])).

cnf(c_12321,plain,
    ( k4_xboole_0(k2_xboole_0(o_0_0_xboole_0,X0),X1) = k2_xboole_0(o_0_0_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_123,c_116])).

cnf(c_85,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f458])).

cnf(c_130,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f489])).

cnf(c_2472,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_130,c_124,c_2])).

cnf(c_6193,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0))) = k2_xboole_0(k4_xboole_0(o_0_0_xboole_0,X0),k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_85,c_2472])).

cnf(c_112,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f478])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f471])).

cnf(c_4659,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_99,c_112])).

cnf(c_6199,plain,
    ( k2_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6193,c_112,c_123,c_4659])).

cnf(c_12384,plain,
    ( k2_xboole_0(o_0_0_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_12321,c_6199])).

cnf(c_12388,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_12316,c_12384])).

cnf(c_14753,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_93,c_93,c_12388])).

cnf(c_14780,plain,
    ( k2_xboole_0(sK16,k4_xboole_0(sK17,k4_xboole_0(sK17,sK15))) = k4_xboole_0(k2_xboole_0(sK16,sK17),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_6707,c_14753])).

cnf(c_14855,plain,
    ( k2_xboole_0(sK16,k4_xboole_0(sK17,k4_xboole_0(sK17,sK15))) = k2_xboole_0(sK16,sK17) ),
    inference(demodulation,[status(thm)],[c_14780,c_112])).

cnf(c_118905,plain,
    ( k2_xboole_0(sK16,sK17) = k2_xboole_0(sK16,o_0_0_xboole_0) ),
    inference(demodulation,[status(thm)],[c_116748,c_14855])).

cnf(c_154,negated_conjecture,
    ( r1_xboole_0(sK18,sK16) ),
    inference(cnf_transformation,[],[f419])).

cnf(c_4550,plain,
    ( r1_xboole_0(sK18,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_116747,plain,
    ( k4_xboole_0(sK18,k4_xboole_0(sK18,sK16)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_4550,c_4632])).

cnf(c_148,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f412])).

cnf(c_8209,plain,
    ( k2_xboole_0(sK17,k2_xboole_0(sK16,sK15)) = k2_xboole_0(sK17,sK18) ),
    inference(superposition,[status(thm)],[c_2468,c_148])).

cnf(c_8217,plain,
    ( k2_xboole_0(sK17,k2_xboole_0(sK16,sK15)) = k2_xboole_0(sK16,sK15) ),
    inference(light_normalisation,[status(thm)],[c_8209,c_2468])).

cnf(c_12222,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_124,c_120])).

cnf(c_74489,plain,
    ( k4_xboole_0(k2_xboole_0(sK17,sK16),k2_xboole_0(sK16,sK15)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_8217,c_12222])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f426])).

cnf(c_76681,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK16,sK15),k2_xboole_0(sK17,sK16))) = k4_xboole_0(k2_xboole_0(sK17,sK16),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_74489,c_3])).

cnf(c_14767,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),k4_xboole_0(sK18,k2_xboole_0(sK17,X0))) = k2_xboole_0(sK17,k4_xboole_0(sK18,k4_xboole_0(sK18,X0))) ),
    inference(superposition,[status(thm)],[c_2468,c_14753])).

cnf(c_14769,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK16,sK15),k2_xboole_0(sK17,X0))) = k2_xboole_0(sK17,k4_xboole_0(k2_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK16,sK15),X0))) ),
    inference(superposition,[status(thm)],[c_8217,c_14753])).

cnf(c_111,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f374])).

cnf(c_7833,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_111,c_2472])).

cnf(c_115,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f378])).

cnf(c_122,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f482])).

cnf(c_4664,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_122,c_115])).

cnf(c_7835,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_7833,c_115,c_4664])).

cnf(c_35,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f298])).

cnf(c_7836,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0))) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_7835,c_35])).

cnf(c_6703,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_120])).

cnf(c_7837,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_7836,c_111,c_112,c_6703])).

cnf(c_6194,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),k4_xboole_0(sK17,k4_xboole_0(sK17,sK18))) = k2_xboole_0(k4_xboole_0(sK18,sK17),k4_xboole_0(sK17,sK18)) ),
    inference(superposition,[status(thm)],[c_2468,c_2472])).

cnf(c_9872,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),k2_xboole_0(k4_xboole_0(sK17,k4_xboole_0(sK17,sK18)),X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK18,sK17),k4_xboole_0(sK17,sK18)),X0) ),
    inference(superposition,[status(thm)],[c_6194,c_115])).

cnf(c_21773,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK18,sK17),k4_xboole_0(sK17,sK18)),k4_xboole_0(sK17,sK18)) = k4_xboole_0(k2_xboole_0(sK16,sK15),k2_xboole_0(k4_xboole_0(sK17,sK18),sK17)) ),
    inference(superposition,[status(thm)],[c_7837,c_9872])).

cnf(c_114,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f377])).

cnf(c_8186,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),sK18) = k4_xboole_0(sK17,sK18) ),
    inference(superposition,[status(thm)],[c_2468,c_114])).

cnf(c_9830,plain,
    ( k4_xboole_0(sK18,k4_xboole_0(sK18,k2_xboole_0(sK16,sK15))) = k4_xboole_0(k2_xboole_0(sK16,sK15),k4_xboole_0(sK17,sK18)) ),
    inference(superposition,[status(thm)],[c_8186,c_3])).

cnf(c_11224,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),k2_xboole_0(k4_xboole_0(sK17,sK18),X0)) = k4_xboole_0(k4_xboole_0(sK18,k4_xboole_0(sK18,k2_xboole_0(sK16,sK15))),X0) ),
    inference(superposition,[status(thm)],[c_9830,c_115])).

cnf(c_11234,plain,
    ( k4_xboole_0(sK18,k2_xboole_0(k4_xboole_0(sK18,k2_xboole_0(sK16,sK15)),X0)) = k4_xboole_0(k2_xboole_0(sK16,sK15),k2_xboole_0(k4_xboole_0(sK17,sK18),X0)) ),
    inference(demodulation,[status(thm)],[c_11224,c_115])).

cnf(c_126,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f485])).

cnf(c_2473,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_126,c_124,c_2])).

cnf(c_11775,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK18,sK17),k4_xboole_0(sK17,sK18)),k4_xboole_0(sK17,k4_xboole_0(sK17,k4_xboole_0(sK17,sK18)))) = k4_xboole_0(k2_xboole_0(sK16,sK15),sK17) ),
    inference(superposition,[status(thm)],[c_2473,c_9872])).

cnf(c_121,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f481])).

cnf(c_11789,plain,
    ( k4_xboole_0(k4_xboole_0(sK18,sK17),k4_xboole_0(sK17,sK18)) = k4_xboole_0(k2_xboole_0(sK16,sK15),sK17) ),
    inference(demodulation,[status(thm)],[c_11775,c_114,c_121])).

cnf(c_18978,plain,
    ( k4_xboole_0(sK18,k2_xboole_0(sK16,sK15)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2468,c_6703])).

cnf(c_21782,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),sK17) = k4_xboole_0(sK18,sK17) ),
    inference(demodulation,[status(thm)],[c_21773,c_114,c_6199,c_11234,c_11789,c_18978])).

cnf(c_22194,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),k2_xboole_0(sK17,X0)) = k4_xboole_0(k4_xboole_0(sK18,sK17),X0) ),
    inference(superposition,[status(thm)],[c_21782,c_115])).

cnf(c_22221,plain,
    ( k4_xboole_0(k2_xboole_0(sK16,sK15),k2_xboole_0(sK17,X0)) = k4_xboole_0(sK18,k2_xboole_0(sK17,X0)) ),
    inference(demodulation,[status(thm)],[c_22194,c_115])).

cnf(c_8188,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_114,c_111])).

cnf(c_8197,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8188,c_111])).

cnf(c_9828,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_114,c_3])).

cnf(c_9854,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_9828,c_112,c_6703])).

cnf(c_28319,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8197,c_9854])).

cnf(c_28447,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),o_0_0_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_28319,c_6703])).

cnf(c_76726,plain,
    ( k2_xboole_0(sK17,k4_xboole_0(sK18,k4_xboole_0(sK18,sK16))) = k2_xboole_0(sK16,sK17) ),
    inference(demodulation,[status(thm)],[c_76681,c_14767,c_14769,c_22221,c_28447])).

cnf(c_118013,plain,
    ( k2_xboole_0(sK16,sK17) = k2_xboole_0(sK17,o_0_0_xboole_0) ),
    inference(demodulation,[status(thm)],[c_116747,c_76726])).

cnf(c_118014,plain,
    ( k2_xboole_0(sK16,sK17) = sK17 ),
    inference(demodulation,[status(thm)],[c_118013,c_85])).

cnf(c_118906,plain,
    ( k2_xboole_0(sK16,o_0_0_xboole_0) = sK17 ),
    inference(light_normalisation,[status(thm)],[c_118905,c_118014])).

cnf(c_118907,plain,
    ( sK17 = sK16 ),
    inference(demodulation,[status(thm)],[c_118906,c_85])).

cnf(c_64,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f329])).

cnf(c_8490,plain,
    ( ~ r1_tarski(X0,sK16)
    | ~ r1_tarski(sK16,X0)
    | sK16 = X0 ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_56087,plain,
    ( ~ r1_tarski(sK16,sK16)
    | sK16 = sK16 ),
    inference(instantiation,[status(thm)],[c_8490])).

cnf(c_2488,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4807,plain,
    ( sK17 != X0
    | sK16 != X0
    | sK16 = sK17 ),
    inference(instantiation,[status(thm)],[c_2488])).

cnf(c_31101,plain,
    ( sK17 != sK16
    | sK16 = sK17
    | sK16 != sK16 ),
    inference(instantiation,[status(thm)],[c_4807])).

cnf(c_66,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f508])).

cnf(c_30477,plain,
    ( r1_tarski(sK16,sK16) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_153,negated_conjecture,
    ( sK16 != sK17 ),
    inference(cnf_transformation,[],[f420])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_118907,c_56087,c_31101,c_30477,c_153])).

%------------------------------------------------------------------------------
