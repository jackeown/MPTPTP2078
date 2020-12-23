%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0472+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 23.26s
% Output     : CNFRefutation 23.26s
% Verified   : 
% Statistics : Number of formulae       :   61 (  97 expanded)
%              Number of clauses        :   21 (  22 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 242 expanded)
%              Number of equality atoms :   82 ( 161 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f706,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f707,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f706])).

fof(f1218,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f707])).

fof(f1219,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1218])).

fof(f1636,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK149
      & ( k1_xboole_0 = k2_relat_1(sK149)
        | k1_xboole_0 = k1_relat_1(sK149) )
      & v1_relat_1(sK149) ) ),
    introduced(choice_axiom,[])).

fof(f1637,plain,
    ( k1_xboole_0 != sK149
    & ( k1_xboole_0 = k2_relat_1(sK149)
      | k1_xboole_0 = k1_relat_1(sK149) )
    & v1_relat_1(sK149) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK149])],[f1219,f1636])).

fof(f2738,plain,
    ( k1_xboole_0 = k2_relat_1(sK149)
    | k1_xboole_0 = k1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f1637])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1645,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3266,plain,
    ( o_0_0_xboole_0 = k2_relat_1(sK149)
    | o_0_0_xboole_0 = k1_relat_1(sK149) ),
    inference(definition_unfolding,[],[f2738,f1645,f1645])).

fof(f672,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1176,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f672])).

fof(f2696,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1176])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1384,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f1385,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1384])).

fof(f2100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1385])).

fof(f3024,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f2100,f1645,f1645])).

fof(f3335,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f3024])).

fof(f662,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1162,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f662])).

fof(f1163,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1162])).

fof(f2684,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1163])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f802,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f1820,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f802])).

fof(f2864,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f1820,f1645])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f778,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f1784,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f778])).

fof(f2838,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f1784,f1645,f1645])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2394,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2331,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f2750,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2331,f1645])).

fof(f3167,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2394,f2750])).

fof(f2739,plain,(
    k1_xboole_0 != sK149 ),
    inference(cnf_transformation,[],[f1637])).

fof(f3265,plain,(
    o_0_0_xboole_0 != sK149 ),
    inference(definition_unfolding,[],[f2739,f1645])).

fof(f2737,plain,(
    v1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f1637])).

cnf(c_14507,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_62648,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK149))
    | k1_relat_1(sK149) != X0 ),
    inference(instantiation,[status(thm)],[c_14507])).

cnf(c_62650,plain,
    ( v1_xboole_0(k1_relat_1(sK149))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_relat_1(sK149) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_62648])).

cnf(c_1086,negated_conjecture,
    ( o_0_0_xboole_0 = k2_relat_1(sK149)
    | o_0_0_xboole_0 = k1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f3266])).

cnf(c_1044,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2696])).

cnf(c_29100,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_50453,plain,
    ( k1_relat_1(sK149) = o_0_0_xboole_0
    | r1_tarski(sK149,k2_zfmisc_1(k1_relat_1(sK149),o_0_0_xboole_0)) = iProver_top
    | v1_relat_1(sK149) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_29100])).

cnf(c_448,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3335])).

cnf(c_50465,plain,
    ( k1_relat_1(sK149) = o_0_0_xboole_0
    | r1_tarski(sK149,o_0_0_xboole_0) = iProver_top
    | v1_relat_1(sK149) != iProver_top ),
    inference(demodulation,[status(thm)],[c_50453,c_448])).

cnf(c_1032,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2684])).

cnf(c_47756,plain,
    ( ~ v1_relat_1(sK149)
    | ~ v1_xboole_0(k1_relat_1(sK149))
    | v1_xboole_0(sK149) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_181,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f2864])).

cnf(c_36917,plain,
    ( ~ v1_xboole_0(sK149)
    | o_0_0_xboole_0 = sK149 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f2838])).

cnf(c_36898,plain,
    ( ~ r1_tarski(sK149,o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK149 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_36899,plain,
    ( o_0_0_xboole_0 = sK149
    | r1_tarski(sK149,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36898])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3167])).

cnf(c_1085,negated_conjecture,
    ( o_0_0_xboole_0 != sK149 ),
    inference(cnf_transformation,[],[f3265])).

cnf(c_1087,negated_conjecture,
    ( v1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f2737])).

cnf(c_1088,plain,
    ( v1_relat_1(sK149) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62650,c_50465,c_47756,c_36917,c_36899,c_743,c_1085,c_1088,c_1087])).

%------------------------------------------------------------------------------
