%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0658+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:49 EST 2020

% Result     : Theorem 38.73s
% Output     : CNFRefutation 38.73s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 177 expanded)
%              Number of clauses        :   33 (  51 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  256 ( 675 expanded)
%              Number of equality atoms :  106 ( 211 expanded)
%              Maximal formula depth    :   11 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1708,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f1709,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1708])).

fof(f3765,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1709])).

fof(f3766,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1709])).

fof(f960,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f961,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f960])).

fof(f1809,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f961])).

fof(f1810,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1809])).

fof(f2386,plain,
    ( ? [X0] :
        ( k2_funct_1(k2_funct_1(X0)) != X0
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( k2_funct_1(k2_funct_1(sK207)) != sK207
      & v2_funct_1(sK207)
      & v1_funct_1(sK207)
      & v1_relat_1(sK207) ) ),
    introduced(choice_axiom,[])).

fof(f2387,plain,
    ( k2_funct_1(k2_funct_1(sK207)) != sK207
    & v2_funct_1(sK207)
    & v1_funct_1(sK207)
    & v1_relat_1(sK207) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK207])],[f1810,f2386])).

fof(f3952,plain,(
    v2_funct_1(sK207) ),
    inference(cnf_transformation,[],[f2387])).

fof(f950,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1789,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f950])).

fof(f1790,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1789])).

fof(f3932,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1790])).

fof(f3931,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1790])).

fof(f3950,plain,(
    v1_relat_1(sK207) ),
    inference(cnf_transformation,[],[f2387])).

fof(f3951,plain,(
    v1_funct_1(sK207) ),
    inference(cnf_transformation,[],[f2387])).

fof(f956,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1801,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f956])).

fof(f1802,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1801])).

fof(f3946,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1802])).

fof(f958,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1805,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f958])).

fof(f1806,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1805])).

fof(f3948,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1806])).

fof(f948,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1785,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f948])).

fof(f1786,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1785])).

fof(f3918,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1786])).

fof(f3953,plain,(
    k2_funct_1(k2_funct_1(sK207)) != sK207 ),
    inference(cnf_transformation,[],[f2387])).

cnf(c_1360,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f3765])).

cnf(c_127855,plain,
    ( ~ v1_funct_1(sK207)
    | v1_relat_1(k2_funct_1(sK207))
    | ~ v1_relat_1(sK207) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_1359,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3766])).

cnf(c_124479,plain,
    ( v1_funct_1(k2_funct_1(sK207))
    | ~ v1_funct_1(sK207)
    | ~ v1_relat_1(sK207) ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_1545,negated_conjecture,
    ( v2_funct_1(sK207) ),
    inference(cnf_transformation,[],[f3952])).

cnf(c_65061,plain,
    ( v2_funct_1(sK207) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_1525,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3932])).

cnf(c_65078,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_118841,plain,
    ( k2_relat_1(k2_funct_1(sK207)) = k1_relat_1(sK207)
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(superposition,[status(thm)],[c_65061,c_65078])).

cnf(c_1526,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f3931])).

cnf(c_65077,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1526])).

cnf(c_113453,plain,
    ( k1_relat_1(k2_funct_1(sK207)) = k2_relat_1(sK207)
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(superposition,[status(thm)],[c_65061,c_65077])).

cnf(c_1547,negated_conjecture,
    ( v1_relat_1(sK207) ),
    inference(cnf_transformation,[],[f3950])).

cnf(c_1553,plain,
    ( v1_relat_1(sK207) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1547])).

cnf(c_1546,negated_conjecture,
    ( v1_funct_1(sK207) ),
    inference(cnf_transformation,[],[f3951])).

cnf(c_1554,plain,
    ( v1_funct_1(sK207) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1546])).

cnf(c_114908,plain,
    ( k1_relat_1(k2_funct_1(sK207)) = k2_relat_1(sK207) ),
    inference(global_propositional_subsumption,[status(thm)],[c_113453,c_1553,c_1554])).

cnf(c_1539,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3946])).

cnf(c_65064,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1539])).

cnf(c_80113,plain,
    ( k5_relat_1(k2_funct_1(sK207),sK207) = k6_relat_1(k2_relat_1(sK207))
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(superposition,[status(thm)],[c_65061,c_65064])).

cnf(c_80243,plain,
    ( k5_relat_1(k2_funct_1(sK207),sK207) = k6_relat_1(k2_relat_1(sK207)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_80113,c_1553,c_1554])).

cnf(c_1542,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f3948])).

cnf(c_1512,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3918])).

cnf(c_7439,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1542,c_1512])).

cnf(c_65055,plain,
    ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7439])).

cnf(c_80247,plain,
    ( k2_funct_1(k2_funct_1(sK207)) = sK207
    | k2_relat_1(k2_funct_1(sK207)) != k1_relat_1(sK207)
    | k6_relat_1(k1_relat_1(k2_funct_1(sK207))) != k6_relat_1(k2_relat_1(sK207))
    | v1_funct_1(k2_funct_1(sK207)) != iProver_top
    | v1_funct_1(sK207) != iProver_top
    | v1_relat_1(k2_funct_1(sK207)) != iProver_top
    | v1_relat_1(sK207) != iProver_top ),
    inference(superposition,[status(thm)],[c_80243,c_65055])).

cnf(c_1544,negated_conjecture,
    ( k2_funct_1(k2_funct_1(sK207)) != sK207 ),
    inference(cnf_transformation,[],[f3953])).

cnf(c_80517,plain,
    ( v1_relat_1(k2_funct_1(sK207)) != iProver_top
    | k2_relat_1(k2_funct_1(sK207)) != k1_relat_1(sK207)
    | k6_relat_1(k1_relat_1(k2_funct_1(sK207))) != k6_relat_1(k2_relat_1(sK207))
    | v1_funct_1(k2_funct_1(sK207)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_80247,c_1553,c_1554,c_1544])).

cnf(c_80518,plain,
    ( k2_relat_1(k2_funct_1(sK207)) != k1_relat_1(sK207)
    | k6_relat_1(k1_relat_1(k2_funct_1(sK207))) != k6_relat_1(k2_relat_1(sK207))
    | v1_funct_1(k2_funct_1(sK207)) != iProver_top
    | v1_relat_1(k2_funct_1(sK207)) != iProver_top ),
    inference(renaming,[status(thm)],[c_80517])).

cnf(c_114911,plain,
    ( k2_relat_1(k2_funct_1(sK207)) != k1_relat_1(sK207)
    | k6_relat_1(k2_relat_1(sK207)) != k6_relat_1(k2_relat_1(sK207))
    | v1_funct_1(k2_funct_1(sK207)) != iProver_top
    | v1_relat_1(k2_funct_1(sK207)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_114908,c_80518])).

cnf(c_114922,plain,
    ( k2_relat_1(k2_funct_1(sK207)) != k1_relat_1(sK207)
    | v1_funct_1(k2_funct_1(sK207)) != iProver_top
    | v1_relat_1(k2_funct_1(sK207)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_114911])).

cnf(c_114930,plain,
    ( ~ v1_funct_1(k2_funct_1(sK207))
    | ~ v1_relat_1(k2_funct_1(sK207))
    | k2_relat_1(k2_funct_1(sK207)) != k1_relat_1(sK207) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_114922])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_127855,c_124479,c_118841,c_114930,c_1554,c_1546,c_1553,c_1547])).

%------------------------------------------------------------------------------
