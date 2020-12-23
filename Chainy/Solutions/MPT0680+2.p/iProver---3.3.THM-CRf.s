%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0680+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:49 EST 2020

% Result     : Theorem 39.14s
% Output     : CNFRefutation 39.14s
% Verified   : 
% Statistics : Number of formulae       :   37 (  76 expanded)
%              Number of clauses        :   16 (  22 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 219 expanded)
%              Number of equality atoms :   43 (  86 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f932,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f933,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f932])).

fof(f1788,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f933])).

fof(f1789,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1788])).

fof(f2437,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK198)
      & ! [X2,X1] : k6_subset_1(k9_relat_1(sK198,X1),k9_relat_1(sK198,X2)) = k9_relat_1(sK198,k6_subset_1(X1,X2))
      & v1_funct_1(sK198)
      & v1_relat_1(sK198) ) ),
    introduced(choice_axiom,[])).

fof(f2438,plain,
    ( ~ v2_funct_1(sK198)
    & ! [X1,X2] : k6_subset_1(k9_relat_1(sK198,X1),k9_relat_1(sK198,X2)) = k9_relat_1(sK198,k6_subset_1(X1,X2))
    & v1_funct_1(sK198)
    & v1_relat_1(sK198) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK198])],[f1789,f2437])).

fof(f3971,plain,(
    ! [X2,X1] : k6_subset_1(k9_relat_1(sK198,X1),k9_relat_1(sK198,X2)) = k9_relat_1(sK198,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f2438])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3275,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f930,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1784,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f930])).

fof(f1785,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1784])).

fof(f2435,plain,(
    ! [X0] :
      ( ? [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) != k9_relat_1(X0,k3_xboole_0(X1,X2))
     => k3_xboole_0(k9_relat_1(X0,sK196(X0)),k9_relat_1(X0,sK197(X0))) != k9_relat_1(X0,k3_xboole_0(sK196(X0),sK197(X0))) ) ),
    introduced(choice_axiom,[])).

fof(f2436,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k3_xboole_0(k9_relat_1(X0,sK196(X0)),k9_relat_1(X0,sK197(X0))) != k9_relat_1(X0,k3_xboole_0(sK196(X0),sK197(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK196,sK197])],[f1785,f2435])).

fof(f3967,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k3_xboole_0(k9_relat_1(X0,sK196(X0)),k9_relat_1(X0,sK197(X0))) != k9_relat_1(X0,k3_xboole_0(sK196(X0),sK197(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2436])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2653,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f4724,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k4_xboole_0(k9_relat_1(X0,sK196(X0)),k4_xboole_0(k9_relat_1(X0,sK196(X0)),k9_relat_1(X0,sK197(X0)))) != k9_relat_1(X0,k4_xboole_0(sK196(X0),k4_xboole_0(sK196(X0),sK197(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3967,f2653,f2653])).

fof(f3972,plain,(
    ~ v2_funct_1(sK198) ),
    inference(cnf_transformation,[],[f2438])).

fof(f3970,plain,(
    v1_funct_1(sK198) ),
    inference(cnf_transformation,[],[f2438])).

fof(f3969,plain,(
    v1_relat_1(sK198) ),
    inference(cnf_transformation,[],[f2438])).

cnf(c_1458,negated_conjecture,
    ( k6_subset_1(k9_relat_1(sK198,X0),k9_relat_1(sK198,X1)) = k9_relat_1(sK198,k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3971])).

cnf(c_764,plain,
    ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3275])).

cnf(c_45952,plain,
    ( k6_subset_1(k9_relat_1(sK198,X0),k9_relat_1(sK198,X1)) = k9_relat_1(sK198,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1458,c_764])).

cnf(c_57862,plain,
    ( k4_xboole_0(k9_relat_1(sK198,X0),k9_relat_1(sK198,X1)) = k9_relat_1(sK198,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_45952,c_764])).

cnf(c_1455,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_xboole_0(k9_relat_1(X0,sK196(X0)),k4_xboole_0(k9_relat_1(X0,sK196(X0)),k9_relat_1(X0,sK197(X0)))) != k9_relat_1(X0,k4_xboole_0(sK196(X0),k4_xboole_0(sK196(X0),sK197(X0)))) ),
    inference(cnf_transformation,[],[f4724])).

cnf(c_44178,plain,
    ( k4_xboole_0(k9_relat_1(X0,sK196(X0)),k4_xboole_0(k9_relat_1(X0,sK196(X0)),k9_relat_1(X0,sK197(X0)))) != k9_relat_1(X0,k4_xboole_0(sK196(X0),k4_xboole_0(sK196(X0),sK197(X0))))
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_118919,plain,
    ( k4_xboole_0(k9_relat_1(sK198,sK196(sK198)),k9_relat_1(sK198,k4_xboole_0(sK196(sK198),sK197(sK198)))) != k9_relat_1(sK198,k4_xboole_0(sK196(sK198),k4_xboole_0(sK196(sK198),sK197(sK198))))
    | v2_funct_1(sK198) = iProver_top
    | v1_funct_1(sK198) != iProver_top
    | v1_relat_1(sK198) != iProver_top ),
    inference(superposition,[status(thm)],[c_57862,c_44178])).

cnf(c_118926,plain,
    ( k9_relat_1(sK198,k4_xboole_0(sK196(sK198),k4_xboole_0(sK196(sK198),sK197(sK198)))) != k9_relat_1(sK198,k4_xboole_0(sK196(sK198),k4_xboole_0(sK196(sK198),sK197(sK198))))
    | v2_funct_1(sK198) = iProver_top
    | v1_funct_1(sK198) != iProver_top
    | v1_relat_1(sK198) != iProver_top ),
    inference(demodulation,[status(thm)],[c_118919,c_57862])).

cnf(c_118927,plain,
    ( v2_funct_1(sK198) = iProver_top
    | v1_funct_1(sK198) != iProver_top
    | v1_relat_1(sK198) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_118926])).

cnf(c_1457,negated_conjecture,
    ( ~ v2_funct_1(sK198) ),
    inference(cnf_transformation,[],[f3972])).

cnf(c_1611,plain,
    ( v2_funct_1(sK198) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_1459,negated_conjecture,
    ( v1_funct_1(sK198) ),
    inference(cnf_transformation,[],[f3970])).

cnf(c_1609,plain,
    ( v1_funct_1(sK198) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_1460,negated_conjecture,
    ( v1_relat_1(sK198) ),
    inference(cnf_transformation,[],[f3969])).

cnf(c_1608,plain,
    ( v1_relat_1(sK198) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_118927,c_1611,c_1609,c_1608])).

%------------------------------------------------------------------------------
