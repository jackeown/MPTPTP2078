%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0655+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:49 EST 2020

% Result     : Theorem 27.68s
% Output     : CNFRefutation 27.68s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 117 expanded)
%              Number of clauses        :   26 (  34 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  190 ( 439 expanded)
%              Number of equality atoms :   63 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f896,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1702,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f1703,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1702])).

fof(f3747,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1703])).

fof(f954,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f955,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f954])).

fof(f1791,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f955])).

fof(f1792,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1791])).

fof(f2368,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(k2_funct_1(X0))
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(k2_funct_1(sK207))
      & v2_funct_1(sK207)
      & v1_funct_1(sK207)
      & v1_relat_1(sK207) ) ),
    introduced(choice_axiom,[])).

fof(f2369,plain,
    ( ~ v2_funct_1(k2_funct_1(sK207))
    & v2_funct_1(sK207)
    & v1_funct_1(sK207)
    & v1_relat_1(sK207) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK207])],[f1792,f2368])).

fof(f3925,plain,(
    v2_funct_1(sK207) ),
    inference(cnf_transformation,[],[f2369])).

fof(f953,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1789,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f953])).

fof(f1790,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1789])).

fof(f3922,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1790])).

fof(f3923,plain,(
    v1_relat_1(sK207) ),
    inference(cnf_transformation,[],[f2369])).

fof(f3924,plain,(
    v1_funct_1(sK207) ),
    inference(cnf_transformation,[],[f2369])).

fof(f945,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1773,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f945])).

fof(f1774,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1773])).

fof(f3894,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1774])).

fof(f947,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1777,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f947])).

fof(f1778,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1777])).

fof(f3907,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1778])).

fof(f3748,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1703])).

fof(f3926,plain,(
    ~ v2_funct_1(k2_funct_1(sK207)) ),
    inference(cnf_transformation,[],[f2369])).

cnf(c_1360,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f3747])).

cnf(c_98880,plain,
    ( ~ v1_funct_1(sK207)
    | v1_relat_1(k2_funct_1(sK207))
    | ~ v1_relat_1(sK207) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_1536,negated_conjecture,
    ( v2_funct_1(sK207) ),
    inference(cnf_transformation,[],[f3925])).

cnf(c_42298,plain,
    ( v2_funct_1(sK207) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_1533,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3922])).

cnf(c_42301,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_56363,plain,
    ( k5_relat_1(k2_funct_1(sK207),sK207) = k6_relat_1(k2_relat_1(sK207))
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(superposition,[status(thm)],[c_42298,c_42301])).

cnf(c_1538,negated_conjecture,
    ( v1_relat_1(sK207) ),
    inference(cnf_transformation,[],[f3923])).

cnf(c_1544,plain,
    ( v1_relat_1(sK207) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1538])).

cnf(c_1537,negated_conjecture,
    ( v1_funct_1(sK207) ),
    inference(cnf_transformation,[],[f3924])).

cnf(c_1545,plain,
    ( v1_funct_1(sK207) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1537])).

cnf(c_56570,plain,
    ( k5_relat_1(k2_funct_1(sK207),sK207) = k6_relat_1(k2_relat_1(sK207)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56363,c_1544,c_1545])).

cnf(c_1506,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3894])).

cnf(c_42325,plain,
    ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_90649,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK207))) != k6_relat_1(k2_relat_1(sK207))
    | v2_funct_1(k2_funct_1(sK207)) = iProver_top
    | v1_funct_1(k2_funct_1(sK207)) != iProver_top
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(k2_funct_1(sK207)) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(superposition,[status(thm)],[c_56570,c_42325])).

cnf(c_1520,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f3907])).

cnf(c_42314,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_76213,plain,
    ( k1_relat_1(k2_funct_1(sK207)) = k2_relat_1(sK207)
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(superposition,[status(thm)],[c_42298,c_42314])).

cnf(c_76716,plain,
    ( k1_relat_1(k2_funct_1(sK207)) = k2_relat_1(sK207) ),
    inference(global_propositional_subsumption,[status(thm)],[c_76213,c_1544,c_1545])).

cnf(c_90661,plain,
    ( k6_relat_1(k2_relat_1(sK207)) != k6_relat_1(k2_relat_1(sK207))
    | v2_funct_1(k2_funct_1(sK207)) = iProver_top
    | v1_funct_1(k2_funct_1(sK207)) != iProver_top
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(k2_funct_1(sK207)) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_90649,c_76716])).

cnf(c_90662,plain,
    ( v2_funct_1(k2_funct_1(sK207)) = iProver_top
    | v1_funct_1(k2_funct_1(sK207)) != iProver_top
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(k2_funct_1(sK207)) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_90661])).

cnf(c_90668,plain,
    ( v2_funct_1(k2_funct_1(sK207))
    | ~ v1_funct_1(k2_funct_1(sK207))
    | ~ v1_funct_1(sK207)
    | ~ v1_relat_1(k2_funct_1(sK207))
    | ~ v1_relat_1(sK207) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_90662])).

cnf(c_1359,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3748])).

cnf(c_68118,plain,
    ( v1_funct_1(k2_funct_1(sK207))
    | ~ v1_funct_1(sK207)
    | ~ v1_relat_1(sK207) ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_1535,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(sK207)) ),
    inference(cnf_transformation,[],[f3926])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98880,c_90668,c_68118,c_1535,c_1537,c_1538])).

%------------------------------------------------------------------------------
