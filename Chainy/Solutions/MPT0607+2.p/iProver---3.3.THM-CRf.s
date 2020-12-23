%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0607+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Theorem 19.59s
% Output     : CNFRefutation 19.59s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 497 expanded)
%              Number of clauses        :   38 ( 150 expanded)
%              Number of leaves         :   10 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  105 ( 957 expanded)
%              Number of equality atoms :   71 ( 501 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f815,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f816,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k1_relat_1(X2),X0)
         => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f815])).

fof(f1521,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) != k7_relat_1(X2,k6_subset_1(X0,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f816])).

fof(f1522,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) != k7_relat_1(X2,k6_subset_1(X0,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1521])).

fof(f2065,plain,
    ( ? [X0,X1,X2] :
        ( k6_subset_1(X2,k7_relat_1(X2,X1)) != k7_relat_1(X2,k6_subset_1(X0,X1))
        & r1_tarski(k1_relat_1(X2),X0)
        & v1_relat_1(X2) )
   => ( k6_subset_1(sK166,k7_relat_1(sK166,sK165)) != k7_relat_1(sK166,k6_subset_1(sK164,sK165))
      & r1_tarski(k1_relat_1(sK166),sK164)
      & v1_relat_1(sK166) ) ),
    introduced(choice_axiom,[])).

fof(f2066,plain,
    ( k6_subset_1(sK166,k7_relat_1(sK166,sK165)) != k7_relat_1(sK166,k6_subset_1(sK164,sK165))
    & r1_tarski(k1_relat_1(sK166),sK164)
    & v1_relat_1(sK166) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK164,sK165,sK166])],[f1522,f2065])).

fof(f3336,plain,(
    v1_relat_1(sK166) ),
    inference(cnf_transformation,[],[f2066])).

fof(f877,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1594,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f877])).

fof(f3418,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1594])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2234,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f4009,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3418,f2234])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2161,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f3435,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f2161,f2234])).

fof(f3337,plain,(
    r1_tarski(k1_relat_1(sK166),sK164) ),
    inference(cnf_transformation,[],[f2066])).

fof(f878,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1595,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f878])).

fof(f1596,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1595])).

fof(f3419,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1596])).

fof(f114,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2238,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f114])).

fof(f3532,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f2238,f2234,f2234,f2234])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2235,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f3529,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f2235,f2234,f2234])).

fof(f341,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2559,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f341])).

fof(f3338,plain,(
    k6_subset_1(sK166,k7_relat_1(sK166,sK165)) != k7_relat_1(sK166,k6_subset_1(sK164,sK165)) ),
    inference(cnf_transformation,[],[f2066])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2856,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

cnf(c_1245,negated_conjecture,
    ( v1_relat_1(sK166) ),
    inference(cnf_transformation,[],[f3336])).

cnf(c_36298,plain,
    ( v1_relat_1(sK166) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_1325,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f4009])).

cnf(c_36237,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_51051,plain,
    ( k4_xboole_0(sK166,k4_xboole_0(sK166,k2_zfmisc_1(X0,k2_relat_1(sK166)))) = k7_relat_1(sK166,X0) ),
    inference(superposition,[status(thm)],[c_36298,c_36237])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3435])).

cnf(c_51619,plain,
    ( k4_xboole_0(sK166,k2_zfmisc_1(X0,k2_relat_1(sK166))) = k5_xboole_0(sK166,k7_relat_1(sK166,X0)) ),
    inference(superposition,[status(thm)],[c_51051,c_1])).

cnf(c_1244,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK166),sK164) ),
    inference(cnf_transformation,[],[f3337])).

cnf(c_36299,plain,
    ( r1_tarski(k1_relat_1(sK166),sK164) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_1326,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f3419])).

cnf(c_36236,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_50092,plain,
    ( k7_relat_1(sK166,sK164) = sK166
    | v1_relat_1(sK166) != iProver_top ),
    inference(superposition,[status(thm)],[c_36299,c_36236])).

cnf(c_1329,plain,
    ( v1_relat_1(sK166) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_50452,plain,
    ( k7_relat_1(sK166,sK164) = sK166 ),
    inference(global_propositional_subsumption,[status(thm)],[c_50092,c_1329])).

cnf(c_158,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f3532])).

cnf(c_52519,plain,
    ( k4_xboole_0(k4_xboole_0(sK166,k5_xboole_0(sK166,k7_relat_1(sK166,X0))),k4_xboole_0(sK166,k4_xboole_0(sK166,X1))) = k4_xboole_0(sK166,k4_xboole_0(sK166,k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK166)),X1))) ),
    inference(superposition,[status(thm)],[c_51619,c_158])).

cnf(c_51621,plain,
    ( k4_xboole_0(sK166,k5_xboole_0(sK166,k7_relat_1(sK166,X0))) = k7_relat_1(sK166,X0) ),
    inference(demodulation,[status(thm)],[c_51619,c_51051])).

cnf(c_52654,plain,
    ( k4_xboole_0(sK166,k4_xboole_0(sK166,k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK166)),X1))) = k4_xboole_0(k7_relat_1(sK166,X0),k4_xboole_0(sK166,k4_xboole_0(sK166,X1))) ),
    inference(light_normalisation,[status(thm)],[c_52519,c_51621])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f3529])).

cnf(c_51618,plain,
    ( k4_xboole_0(sK166,k4_xboole_0(sK166,k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK166)),X1))) = k4_xboole_0(k7_relat_1(sK166,X0),X1) ),
    inference(superposition,[status(thm)],[c_51051,c_155])).

cnf(c_51895,plain,
    ( k4_xboole_0(sK166,k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK166)),X1)) = k5_xboole_0(sK166,k4_xboole_0(k7_relat_1(sK166,X0),X1)) ),
    inference(superposition,[status(thm)],[c_51618,c_1])).

cnf(c_51897,plain,
    ( k4_xboole_0(sK166,k5_xboole_0(sK166,k4_xboole_0(k7_relat_1(sK166,X0),X1))) = k4_xboole_0(k7_relat_1(sK166,X0),X1) ),
    inference(demodulation,[status(thm)],[c_51895,c_51618])).

cnf(c_55797,plain,
    ( k4_xboole_0(k7_relat_1(sK166,X0),k4_xboole_0(sK166,k4_xboole_0(sK166,X1))) = k4_xboole_0(k7_relat_1(sK166,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_52654,c_51895,c_51897])).

cnf(c_55801,plain,
    ( k4_xboole_0(sK166,k4_xboole_0(sK166,k4_xboole_0(sK166,X0))) = k4_xboole_0(k7_relat_1(sK166,sK164),X0) ),
    inference(superposition,[status(thm)],[c_50452,c_55797])).

cnf(c_55903,plain,
    ( k4_xboole_0(sK166,k4_xboole_0(sK166,k4_xboole_0(sK166,X0))) = k4_xboole_0(sK166,X0) ),
    inference(light_normalisation,[status(thm)],[c_55801,c_50452])).

cnf(c_56214,plain,
    ( k4_xboole_0(sK166,k4_xboole_0(sK166,k5_xboole_0(sK166,k7_relat_1(sK166,X0)))) = k4_xboole_0(sK166,k2_zfmisc_1(X0,k2_relat_1(sK166))) ),
    inference(superposition,[status(thm)],[c_51619,c_55903])).

cnf(c_56638,plain,
    ( k4_xboole_0(sK166,k7_relat_1(sK166,X0)) = k5_xboole_0(sK166,k7_relat_1(sK166,X0)) ),
    inference(light_normalisation,[status(thm)],[c_56214,c_51619,c_51621])).

cnf(c_469,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f2559])).

cnf(c_51889,plain,
    ( k4_xboole_0(sK166,k4_xboole_0(sK166,k2_zfmisc_1(k4_xboole_0(X0,X1),k2_relat_1(sK166)))) = k4_xboole_0(k7_relat_1(sK166,X0),k2_zfmisc_1(X1,k2_relat_1(sK166))) ),
    inference(superposition,[status(thm)],[c_469,c_51618])).

cnf(c_52022,plain,
    ( k4_xboole_0(k7_relat_1(sK166,X0),k2_zfmisc_1(X1,k2_relat_1(sK166))) = k7_relat_1(sK166,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_51889,c_51619,c_51621])).

cnf(c_52177,plain,
    ( k4_xboole_0(sK166,k2_zfmisc_1(X0,k2_relat_1(sK166))) = k7_relat_1(sK166,k4_xboole_0(sK164,X0)) ),
    inference(superposition,[status(thm)],[c_50452,c_52022])).

cnf(c_52202,plain,
    ( k7_relat_1(sK166,k4_xboole_0(sK164,X0)) = k5_xboole_0(sK166,k7_relat_1(sK166,X0)) ),
    inference(light_normalisation,[status(thm)],[c_52177,c_51619])).

cnf(c_1243,negated_conjecture,
    ( k6_subset_1(sK166,k7_relat_1(sK166,sK165)) != k7_relat_1(sK166,k6_subset_1(sK164,sK165)) ),
    inference(cnf_transformation,[],[f3338])).

cnf(c_764,plain,
    ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2856])).

cnf(c_37527,plain,
    ( k7_relat_1(sK166,k4_xboole_0(sK164,sK165)) != k4_xboole_0(sK166,k7_relat_1(sK166,sK165)) ),
    inference(demodulation,[status(thm)],[c_1243,c_764])).

cnf(c_53035,plain,
    ( k4_xboole_0(sK166,k7_relat_1(sK166,sK165)) != k5_xboole_0(sK166,k7_relat_1(sK166,sK165)) ),
    inference(demodulation,[status(thm)],[c_52202,c_37527])).

cnf(c_57640,plain,
    ( k5_xboole_0(sK166,k7_relat_1(sK166,sK165)) != k5_xboole_0(sK166,k7_relat_1(sK166,sK165)) ),
    inference(demodulation,[status(thm)],[c_56638,c_53035])).

cnf(c_57642,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_57640])).

%------------------------------------------------------------------------------
