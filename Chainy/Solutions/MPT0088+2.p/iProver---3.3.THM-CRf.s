%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0088+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:19 EST 2020

% Result     : Theorem 10.30s
% Output     : CNFRefutation 10.30s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of clauses        :   23 (  24 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :   69 (  91 expanded)
%              Number of equality atoms :   34 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f392,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f281,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f127,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f128,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f127])).

fof(f219,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f128])).

fof(f277,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK16,k4_xboole_0(sK15,sK17))
      & r1_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ) ),
    introduced(choice_axiom,[])).

fof(f278,plain,
    ( ~ r1_xboole_0(sK16,k4_xboole_0(sK15,sK17))
    & r1_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f219,f277])).

fof(f446,plain,(
    r1_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f278])).

fof(f122,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f216,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f122])).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f216])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f403,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f526,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f441,f403,f403])).

fof(f86,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f402,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f506,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f402,f403])).

fof(f80,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f396,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f80])).

fof(f123,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f442,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f123])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f141,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f322,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f447,plain,(
    ~ r1_xboole_0(sK16,k4_xboole_0(sK15,sK17)) ),
    inference(cnf_transformation,[],[f278])).

cnf(c_111,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f392])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f281])).

cnf(c_165,negated_conjecture,
    ( r1_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f446])).

cnf(c_4992,plain,
    ( r1_xboole_0(sK15,k4_xboole_0(sK16,sK17)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_159,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f526])).

cnf(c_4997,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2))
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_6781,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(k4_xboole_0(sK16,sK17),X0))) = k4_xboole_0(sK15,k4_xboole_0(sK15,X0)) ),
    inference(superposition,[status(thm)],[c_4992,c_4997])).

cnf(c_121,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f506])).

cnf(c_8289,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK15,X0))) = k4_xboole_0(sK15,k2_xboole_0(k4_xboole_0(sK16,sK17),X0)) ),
    inference(superposition,[status(thm)],[c_6781,c_121])).

cnf(c_8296,plain,
    ( k4_xboole_0(sK15,k2_xboole_0(k4_xboole_0(sK16,sK17),X0)) = k4_xboole_0(sK15,X0) ),
    inference(demodulation,[status(thm)],[c_8289,c_121])).

cnf(c_8304,plain,
    ( k4_xboole_0(sK15,k2_xboole_0(X0,k4_xboole_0(sK16,sK17))) = k4_xboole_0(sK15,X0) ),
    inference(superposition,[status(thm)],[c_2,c_8296])).

cnf(c_10160,plain,
    ( k4_xboole_0(sK15,k2_xboole_0(sK17,sK16)) = k4_xboole_0(sK15,sK17) ),
    inference(superposition,[status(thm)],[c_111,c_8304])).

cnf(c_115,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f396])).

cnf(c_160,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f442])).

cnf(c_4996,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_7501,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_115,c_4996])).

cnf(c_44048,plain,
    ( r1_xboole_0(k4_xboole_0(sK15,sK17),sK16) = iProver_top ),
    inference(superposition,[status(thm)],[c_10160,c_7501])).

cnf(c_41,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f322])).

cnf(c_6001,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK15,sK17),sK16)
    | r1_xboole_0(sK16,k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_6002,plain,
    ( r1_xboole_0(k4_xboole_0(sK15,sK17),sK16) != iProver_top
    | r1_xboole_0(sK16,k4_xboole_0(sK15,sK17)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6001])).

cnf(c_164,negated_conjecture,
    ( ~ r1_xboole_0(sK16,k4_xboole_0(sK15,sK17)) ),
    inference(cnf_transformation,[],[f447])).

cnf(c_170,plain,
    ( r1_xboole_0(sK16,k4_xboole_0(sK15,sK17)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44048,c_6002,c_170])).

%------------------------------------------------------------------------------
