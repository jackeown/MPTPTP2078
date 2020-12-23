%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0362+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 27.97s
% Output     : CNFRefutation 27.97s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 109 expanded)
%              Number of clauses        :   29 (  35 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 247 expanded)
%              Number of equality atoms :   43 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f504,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f503])).

fof(f802,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f504])).

fof(f1039,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,sK73)))
        & m1_subset_1(sK73,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1038,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k9_subset_1(sK71,sK72,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK71)) )
      & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ) ),
    introduced(choice_axiom,[])).

fof(f1040,plain,
    ( ~ r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k9_subset_1(sK71,sK72,sK73)))
    & m1_subset_1(sK73,k1_zfmisc_1(sK71))
    & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK71,sK72,sK73])],[f802,f1039,f1038])).

fof(f1780,plain,(
    m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1040])).

fof(f484,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f776,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f484])).

fof(f1743,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f776])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1202,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f2209,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f1743,f1202])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1201,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f1895,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1201,f1202])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1129,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1802,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f1129,f1202])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1187,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f493,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f789,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f493])).

fof(f1035,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f789])).

fof(f1766,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1035])).

fof(f1781,plain,(
    ~ r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k9_subset_1(sK71,sK72,sK73))) ),
    inference(cnf_transformation,[],[f1040])).

fof(f1779,plain,(
    m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1040])).

fof(f467,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f762,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f467])).

fof(f1725,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f762])).

cnf(c_719,negated_conjecture,
    ( m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1780])).

cnf(c_17361,plain,
    ( m1_subset_1(sK73,k1_zfmisc_1(sK71)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f2209])).

cnf(c_17395,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1895])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1802])).

cnf(c_23442,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_154,c_1])).

cnf(c_111273,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17395,c_23442])).

cnf(c_111283,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,sK73)) = k9_subset_1(sK71,X0,sK73) ),
    inference(superposition,[status(thm)],[c_17361,c_111273])).

cnf(c_140,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1187])).

cnf(c_17711,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_49623,plain,
    ( r1_tarski(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23442,c_17711])).

cnf(c_112149,plain,
    ( r1_tarski(k9_subset_1(sK71,X0,sK73),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_111283,c_49623])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f1766])).

cnf(c_17372,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_718,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k9_subset_1(sK71,sK72,sK73))) ),
    inference(cnf_transformation,[],[f1781])).

cnf(c_17362,plain,
    ( r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k9_subset_1(sK71,sK72,sK73))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_62595,plain,
    ( m1_subset_1(k9_subset_1(sK71,sK72,sK73),k1_zfmisc_1(sK71)) != iProver_top
    | m1_subset_1(sK72,k1_zfmisc_1(sK71)) != iProver_top
    | r1_tarski(k9_subset_1(sK71,sK72,sK73),sK72) != iProver_top ),
    inference(superposition,[status(thm)],[c_17372,c_17362])).

cnf(c_720,negated_conjecture,
    ( m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1779])).

cnf(c_728,plain,
    ( m1_subset_1(sK72,k1_zfmisc_1(sK71)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_729,plain,
    ( m1_subset_1(sK73,k1_zfmisc_1(sK71)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_730,plain,
    ( r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k9_subset_1(sK71,sK72,sK73))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_23081,plain,
    ( ~ m1_subset_1(k9_subset_1(sK71,sK72,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | ~ r1_tarski(k9_subset_1(sK71,sK72,sK73),sK72)
    | r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k9_subset_1(sK71,sK72,sK73))) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_23082,plain,
    ( m1_subset_1(k9_subset_1(sK71,sK72,sK73),k1_zfmisc_1(sK71)) != iProver_top
    | m1_subset_1(sK72,k1_zfmisc_1(sK71)) != iProver_top
    | r1_tarski(k9_subset_1(sK71,sK72,sK73),sK72) != iProver_top
    | r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k9_subset_1(sK71,sK72,sK73))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23081])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1725])).

cnf(c_28162,plain,
    ( m1_subset_1(k9_subset_1(sK71,sK72,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_28163,plain,
    ( m1_subset_1(k9_subset_1(sK71,sK72,sK73),k1_zfmisc_1(sK71)) = iProver_top
    | m1_subset_1(sK73,k1_zfmisc_1(sK71)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28162])).

cnf(c_64335,plain,
    ( r1_tarski(k9_subset_1(sK71,sK72,sK73),sK72) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62595,c_728,c_729,c_730,c_23082,c_28163])).

cnf(c_114143,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_112149,c_64335])).

%------------------------------------------------------------------------------
