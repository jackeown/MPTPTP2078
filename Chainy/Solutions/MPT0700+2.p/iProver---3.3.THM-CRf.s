%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0700+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 43.73s
% Output     : CNFRefutation 43.73s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 306 expanded)
%              Number of clauses        :   47 (  97 expanded)
%              Number of leaves         :    9 (  58 expanded)
%              Depth                    :   20
%              Number of atoms          :  320 (1120 expanded)
%              Number of equality atoms :  147 ( 353 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f956,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f957,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f956])).

fof(f1853,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) != k10_relat_1(X1,X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f957])).

fof(f1854,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) != k10_relat_1(X1,X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1853])).

fof(f2515,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k2_funct_1(X1),X0) != k10_relat_1(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(k2_funct_1(sK206),sK205) != k10_relat_1(sK206,sK205)
      & v2_funct_1(sK206)
      & v1_funct_1(sK206)
      & v1_relat_1(sK206) ) ),
    introduced(choice_axiom,[])).

fof(f2516,plain,
    ( k9_relat_1(k2_funct_1(sK206),sK205) != k10_relat_1(sK206,sK205)
    & v2_funct_1(sK206)
    & v1_funct_1(sK206)
    & v1_relat_1(sK206) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK205,sK206])],[f1854,f2515])).

fof(f4082,plain,(
    v2_funct_1(sK206) ),
    inference(cnf_transformation,[],[f2516])).

fof(f997,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1927,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f997])).

fof(f1928,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1927])).

fof(f4192,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1928])).

fof(f4080,plain,(
    v1_relat_1(sK206) ),
    inference(cnf_transformation,[],[f2516])).

fof(f4081,plain,(
    v1_funct_1(sK206) ),
    inference(cnf_transformation,[],[f2516])).

fof(f984,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1901,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f984])).

fof(f1902,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1901])).

fof(f4159,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1902])).

fof(f986,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1905,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f986])).

fof(f1906,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1905])).

fof(f4172,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1906])).

fof(f898,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1763,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f898])).

fof(f1764,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1763])).

fof(f3963,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1764])).

fof(f3964,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1764])).

fof(f992,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1917,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f992])).

fof(f1918,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1917])).

fof(f4187,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1918])).

fof(f955,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1851,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f955])).

fof(f1852,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1851])).

fof(f4079,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1852])).

fof(f996,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1925,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f996])).

fof(f1926,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1925])).

fof(f4191,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1926])).

fof(f4083,plain,(
    k9_relat_1(k2_funct_1(sK206),sK205) != k10_relat_1(sK206,sK205) ),
    inference(cnf_transformation,[],[f2516])).

cnf(c_1491,negated_conjecture,
    ( v2_funct_1(sK206) ),
    inference(cnf_transformation,[],[f4082])).

cnf(c_45116,plain,
    ( v2_funct_1(sK206) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1491])).

cnf(c_1602,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4192])).

cnf(c_45022,plain,
    ( k5_relat_1(k2_funct_1(X0),k2_funct_1(X1)) = k2_funct_1(k5_relat_1(X1,X0))
    | v2_funct_1(X1) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_59505,plain,
    ( k5_relat_1(k2_funct_1(sK206),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK206))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(superposition,[status(thm)],[c_45116,c_45022])).

cnf(c_1493,negated_conjecture,
    ( v1_relat_1(sK206) ),
    inference(cnf_transformation,[],[f4080])).

cnf(c_1639,plain,
    ( v1_relat_1(sK206) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_1492,negated_conjecture,
    ( v1_funct_1(sK206) ),
    inference(cnf_transformation,[],[f4081])).

cnf(c_1640,plain,
    ( v1_funct_1(sK206) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_59710,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK206),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK206))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59505,c_1639,c_1640])).

cnf(c_59711,plain,
    ( k5_relat_1(k2_funct_1(sK206),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK206))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_59710])).

cnf(c_59722,plain,
    ( k5_relat_1(k2_funct_1(sK206),k2_funct_1(sK206)) = k2_funct_1(k5_relat_1(sK206,sK206))
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(superposition,[status(thm)],[c_45116,c_59711])).

cnf(c_59841,plain,
    ( k5_relat_1(k2_funct_1(sK206),k2_funct_1(sK206)) = k2_funct_1(k5_relat_1(sK206,sK206)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_59722,c_1639,c_1640])).

cnf(c_1569,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4159])).

cnf(c_45050,plain,
    ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_111994,plain,
    ( k2_funct_1(k5_relat_1(sK206,sK206)) != k6_relat_1(k1_relat_1(k2_funct_1(sK206)))
    | v2_funct_1(k2_funct_1(sK206)) = iProver_top
    | v1_funct_1(k2_funct_1(sK206)) != iProver_top
    | v1_relat_1(k2_funct_1(sK206)) != iProver_top ),
    inference(superposition,[status(thm)],[c_59841,c_45050])).

cnf(c_1583,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f4172])).

cnf(c_45039,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_93586,plain,
    ( k1_relat_1(k2_funct_1(sK206)) = k2_relat_1(sK206)
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(superposition,[status(thm)],[c_45116,c_45039])).

cnf(c_93700,plain,
    ( k1_relat_1(k2_funct_1(sK206)) = k2_relat_1(sK206) ),
    inference(global_propositional_subsumption,[status(thm)],[c_93586,c_1639,c_1640])).

cnf(c_112393,plain,
    ( k2_funct_1(k5_relat_1(sK206,sK206)) != k6_relat_1(k2_relat_1(sK206))
    | v2_funct_1(k2_funct_1(sK206)) = iProver_top
    | v1_funct_1(k2_funct_1(sK206)) != iProver_top
    | v1_relat_1(k2_funct_1(sK206)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_111994,c_93700])).

cnf(c_1374,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f3963])).

cnf(c_78509,plain,
    ( ~ v1_funct_1(sK206)
    | v1_relat_1(k2_funct_1(sK206))
    | ~ v1_relat_1(sK206) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_78510,plain,
    ( v1_funct_1(sK206) != iProver_top
    | v1_relat_1(k2_funct_1(sK206)) = iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78509])).

cnf(c_1373,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3964])).

cnf(c_78520,plain,
    ( v1_funct_1(k2_funct_1(sK206))
    | ~ v1_funct_1(sK206)
    | ~ v1_relat_1(sK206) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_78521,plain,
    ( v1_funct_1(k2_funct_1(sK206)) = iProver_top
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78520])).

cnf(c_1596,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4187])).

cnf(c_45026,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1596])).

cnf(c_62601,plain,
    ( k5_relat_1(k2_funct_1(sK206),sK206) = k6_relat_1(k2_relat_1(sK206))
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(superposition,[status(thm)],[c_45116,c_45026])).

cnf(c_62903,plain,
    ( k5_relat_1(k2_funct_1(sK206),sK206) = k6_relat_1(k2_relat_1(sK206)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62601,c_1639,c_1640])).

cnf(c_112004,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK206))) != k6_relat_1(k2_relat_1(sK206))
    | v2_funct_1(k2_funct_1(sK206)) = iProver_top
    | v1_funct_1(k2_funct_1(sK206)) != iProver_top
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(k2_funct_1(sK206)) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(superposition,[status(thm)],[c_62903,c_45050])).

cnf(c_112278,plain,
    ( k6_relat_1(k2_relat_1(sK206)) != k6_relat_1(k2_relat_1(sK206))
    | v2_funct_1(k2_funct_1(sK206)) = iProver_top
    | v1_funct_1(k2_funct_1(sK206)) != iProver_top
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(k2_funct_1(sK206)) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_112004,c_93700])).

cnf(c_112279,plain,
    ( v2_funct_1(k2_funct_1(sK206)) = iProver_top
    | v1_funct_1(k2_funct_1(sK206)) != iProver_top
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(k2_funct_1(sK206)) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_112278])).

cnf(c_115239,plain,
    ( v2_funct_1(k2_funct_1(sK206)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_112393,c_1639,c_1640,c_78510,c_78521,c_112279])).

cnf(c_1489,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f4079])).

cnf(c_45117,plain,
    ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_134610,plain,
    ( k10_relat_1(k2_funct_1(k2_funct_1(sK206)),X0) = k9_relat_1(k2_funct_1(sK206),X0)
    | v1_funct_1(k2_funct_1(sK206)) != iProver_top
    | v1_relat_1(k2_funct_1(sK206)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115239,c_45117])).

cnf(c_1601,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4191])).

cnf(c_45023,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1601])).

cnf(c_60107,plain,
    ( k2_funct_1(k2_funct_1(sK206)) = sK206
    | v1_funct_1(sK206) != iProver_top
    | v1_relat_1(sK206) != iProver_top ),
    inference(superposition,[status(thm)],[c_45116,c_45023])).

cnf(c_60681,plain,
    ( k2_funct_1(k2_funct_1(sK206)) = sK206 ),
    inference(global_propositional_subsumption,[status(thm)],[c_60107,c_1639,c_1640])).

cnf(c_134614,plain,
    ( k9_relat_1(k2_funct_1(sK206),X0) = k10_relat_1(sK206,X0)
    | v1_funct_1(k2_funct_1(sK206)) != iProver_top
    | v1_relat_1(k2_funct_1(sK206)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_134610,c_60681])).

cnf(c_135575,plain,
    ( k9_relat_1(k2_funct_1(sK206),X0) = k10_relat_1(sK206,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_134614,c_1639,c_1640,c_78510,c_78521])).

cnf(c_1490,negated_conjecture,
    ( k9_relat_1(k2_funct_1(sK206),sK205) != k10_relat_1(sK206,sK205) ),
    inference(cnf_transformation,[],[f4083])).

cnf(c_135579,plain,
    ( k10_relat_1(sK206,sK205) != k10_relat_1(sK206,sK205) ),
    inference(demodulation,[status(thm)],[c_135575,c_1490])).

cnf(c_135580,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_135579])).

%------------------------------------------------------------------------------
