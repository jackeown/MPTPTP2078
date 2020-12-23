%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0722+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 50.99s
% Output     : CNFRefutation 50.99s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 110 expanded)
%              Number of clauses        :   21 (  26 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 487 expanded)
%              Number of equality atoms :   46 ( 123 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f999,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1000,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f999])).

fof(f1964,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1000])).

fof(f1965,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1964])).

fof(f2658,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
     => ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,sK219)) != sK219
        & r1_tarski(sK219,k1_relat_1(X0))
        & v2_funct_1(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2657,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
            & r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(k2_funct_1(sK218),k9_relat_1(sK218,X1)) != X1
          & r1_tarski(X1,k1_relat_1(sK218))
          & v2_funct_1(sK218) )
      & v1_funct_1(sK218)
      & v1_relat_1(sK218) ) ),
    introduced(choice_axiom,[])).

fof(f2659,plain,
    ( k9_relat_1(k2_funct_1(sK218),k9_relat_1(sK218,sK219)) != sK219
    & r1_tarski(sK219,k1_relat_1(sK218))
    & v2_funct_1(sK218)
    & v1_funct_1(sK218)
    & v1_relat_1(sK218) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK218,sK219])],[f1965,f2658,f2657])).

fof(f4296,plain,(
    v2_funct_1(sK218) ),
    inference(cnf_transformation,[],[f2659])).

fof(f975,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1918,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f975])).

fof(f1919,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1918])).

fof(f4255,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1919])).

fof(f4294,plain,(
    v1_relat_1(sK218) ),
    inference(cnf_transformation,[],[f2659])).

fof(f4295,plain,(
    v1_funct_1(sK218) ),
    inference(cnf_transformation,[],[f2659])).

fof(f4298,plain,(
    k9_relat_1(k2_funct_1(sK218),k9_relat_1(sK218,sK219)) != sK219 ),
    inference(cnf_transformation,[],[f2659])).

fof(f4297,plain,(
    r1_tarski(sK219,k1_relat_1(sK218)) ),
    inference(cnf_transformation,[],[f2659])).

fof(f985,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1936,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f985])).

fof(f1937,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1936])).

fof(f4269,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1937])).

cnf(c_1568,negated_conjecture,
    ( v2_funct_1(sK218) ),
    inference(cnf_transformation,[],[f4296])).

cnf(c_71731,plain,
    ( v2_funct_1(sK218) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_1527,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f4255])).

cnf(c_71765,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1527])).

cnf(c_202706,plain,
    ( k9_relat_1(k2_funct_1(sK218),X0) = k10_relat_1(sK218,X0)
    | v1_funct_1(sK218) != iProver_top
    | v1_relat_1(sK218) != iProver_top ),
    inference(superposition,[status(thm)],[c_71731,c_71765])).

cnf(c_1570,negated_conjecture,
    ( v1_relat_1(sK218) ),
    inference(cnf_transformation,[],[f4294])).

cnf(c_1705,plain,
    ( v1_relat_1(sK218) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_1569,negated_conjecture,
    ( v1_funct_1(sK218) ),
    inference(cnf_transformation,[],[f4295])).

cnf(c_1706,plain,
    ( v1_funct_1(sK218) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_203108,plain,
    ( k9_relat_1(k2_funct_1(sK218),X0) = k10_relat_1(sK218,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_202706,c_1705,c_1706])).

cnf(c_1566,negated_conjecture,
    ( k9_relat_1(k2_funct_1(sK218),k9_relat_1(sK218,sK219)) != sK219 ),
    inference(cnf_transformation,[],[f4298])).

cnf(c_203113,plain,
    ( k10_relat_1(sK218,k9_relat_1(sK218,sK219)) != sK219 ),
    inference(demodulation,[status(thm)],[c_203108,c_1566])).

cnf(c_1567,negated_conjecture,
    ( r1_tarski(sK219,k1_relat_1(sK218)) ),
    inference(cnf_transformation,[],[f4297])).

cnf(c_71732,plain,
    ( r1_tarski(sK219,k1_relat_1(sK218)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_1541,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f4269])).

cnf(c_71754,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_181032,plain,
    ( k10_relat_1(sK218,k9_relat_1(sK218,sK219)) = sK219
    | v2_funct_1(sK218) != iProver_top
    | v1_funct_1(sK218) != iProver_top
    | v1_relat_1(sK218) != iProver_top ),
    inference(superposition,[status(thm)],[c_71732,c_71754])).

cnf(c_93744,plain,
    ( ~ r1_tarski(sK219,k1_relat_1(sK218))
    | ~ v2_funct_1(sK218)
    | ~ v1_funct_1(sK218)
    | ~ v1_relat_1(sK218)
    | k10_relat_1(sK218,k9_relat_1(sK218,sK219)) = sK219 ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_182410,plain,
    ( k10_relat_1(sK218,k9_relat_1(sK218,sK219)) = sK219 ),
    inference(global_propositional_subsumption,[status(thm)],[c_181032,c_1570,c_1569,c_1568,c_1567,c_93744])).

cnf(c_203194,plain,
    ( sK219 != sK219 ),
    inference(light_normalisation,[status(thm)],[c_203113,c_182410])).

cnf(c_203195,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_203194])).

%------------------------------------------------------------------------------
