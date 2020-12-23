%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0633+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 19.42s
% Output     : CNFRefutation 19.42s
% Verified   : 
% Statistics : Number of formulae       :   33 (  50 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 202 expanded)
%              Number of equality atoms :   60 ( 105 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f921,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f922,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(negated_conjecture,[],[f921])).

fof(f1703,plain,(
    ? [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) != X0
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f922])).

fof(f2244,plain,
    ( ? [X0,X1] :
        ( k1_funct_1(k6_relat_1(X1),X0) != X0
        & r2_hidden(X0,X1) )
   => ( k1_funct_1(k6_relat_1(sK194),sK193) != sK193
      & r2_hidden(sK193,sK194) ) ),
    introduced(choice_axiom,[])).

fof(f2245,plain,
    ( k1_funct_1(k6_relat_1(sK194),sK193) != sK193
    & r2_hidden(sK193,sK194) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK193,sK194])],[f1703,f2244])).

fof(f3712,plain,(
    r2_hidden(sK193,sK194) ),
    inference(cnf_transformation,[],[f2245])).

fof(f920,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1701,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f920])).

fof(f1702,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1701])).

fof(f2239,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1702])).

fof(f2240,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2239])).

fof(f2241,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f2240])).

fof(f2242,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK192(X0,X1)) != sK192(X0,X1)
        & r2_hidden(sK192(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2243,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK192(X0,X1)) != sK192(X0,X1)
            & r2_hidden(sK192(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK192])],[f2241,f2242])).

fof(f3709,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2243])).

fof(f4544,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f3709])).

fof(f897,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3622,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f897])).

fof(f3623,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f897])).

fof(f3713,plain,(
    k1_funct_1(k6_relat_1(sK194),sK193) != sK193 ),
    inference(cnf_transformation,[],[f2245])).

cnf(c_1449,negated_conjecture,
    ( r2_hidden(sK193,sK194) ),
    inference(cnf_transformation,[],[f3712])).

cnf(c_59856,plain,
    ( r2_hidden(sK193,sK194) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_1446,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f4544])).

cnf(c_59857,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1446])).

cnf(c_1359,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3622])).

cnf(c_1701,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_1358,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3623])).

cnf(c_61960,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1358,c_1446])).

cnf(c_61961,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61960])).

cnf(c_63270,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59857,c_1701,c_61961])).

cnf(c_63274,plain,
    ( k1_funct_1(k6_relat_1(sK194),sK193) = sK193 ),
    inference(superposition,[status(thm)],[c_59856,c_63270])).

cnf(c_1448,negated_conjecture,
    ( k1_funct_1(k6_relat_1(sK194),sK193) != sK193 ),
    inference(cnf_transformation,[],[f3713])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63274,c_1448])).

%------------------------------------------------------------------------------
