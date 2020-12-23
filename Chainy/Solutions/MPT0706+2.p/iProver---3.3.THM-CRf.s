%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0706+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 51.94s
% Output     : CNFRefutation 51.94s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 119 expanded)
%              Number of clauses        :   25 (  34 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 550 expanded)
%              Number of equality atoms :   60 ( 193 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2051,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2052,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2051])).

fof(f2666,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2052])).

fof(f4913,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2666])).

fof(f964,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X1,k2_relat_1(X2))
          & r1_tarski(X0,k2_relat_1(X2))
          & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f965,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X1,k2_relat_1(X2))
            & r1_tarski(X0,k2_relat_1(X2))
            & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f964])).

fof(f1873,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f965])).

fof(f1874,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1873])).

fof(f2541,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r1_tarski(X1,k2_relat_1(X2))
        & r1_tarski(X0,k2_relat_1(X2))
        & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK208 != sK209
      & r1_tarski(sK209,k2_relat_1(sK210))
      & r1_tarski(sK208,k2_relat_1(sK210))
      & k10_relat_1(sK210,sK208) = k10_relat_1(sK210,sK209)
      & v1_funct_1(sK210)
      & v1_relat_1(sK210) ) ),
    introduced(choice_axiom,[])).

fof(f2542,plain,
    ( sK208 != sK209
    & r1_tarski(sK209,k2_relat_1(sK210))
    & r1_tarski(sK208,k2_relat_1(sK210))
    & k10_relat_1(sK210,sK208) = k10_relat_1(sK210,sK209)
    & v1_funct_1(sK210)
    & v1_relat_1(sK210) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK208,sK209,sK210])],[f1874,f2541])).

fof(f4117,plain,(
    k10_relat_1(sK210,sK208) = k10_relat_1(sK210,sK209) ),
    inference(cnf_transformation,[],[f2542])).

fof(f960,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1866,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f960])).

fof(f1867,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1866])).

fof(f4107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1867])).

fof(f4115,plain,(
    v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f2542])).

fof(f4116,plain,(
    v1_funct_1(sK210) ),
    inference(cnf_transformation,[],[f2542])).

fof(f4119,plain,(
    r1_tarski(sK209,k2_relat_1(sK210)) ),
    inference(cnf_transformation,[],[f2542])).

fof(f2668,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2052])).

fof(f4120,plain,(
    sK208 != sK209 ),
    inference(cnf_transformation,[],[f2542])).

fof(f4118,plain,(
    r1_tarski(sK208,k2_relat_1(sK210)) ),
    inference(cnf_transformation,[],[f2542])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4913])).

cnf(c_46367,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_1504,negated_conjecture,
    ( k10_relat_1(sK210,sK208) = k10_relat_1(sK210,sK209) ),
    inference(cnf_transformation,[],[f4117])).

cnf(c_1493,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_relat_1(X2))
    | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f4107])).

cnf(c_45384,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_relat_1(X2)) != iProver_top
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_207061,plain,
    ( r1_tarski(X0,k2_relat_1(sK210)) != iProver_top
    | r1_tarski(X0,sK209) = iProver_top
    | r1_tarski(k10_relat_1(sK210,X0),k10_relat_1(sK210,sK208)) != iProver_top
    | v1_funct_1(sK210) != iProver_top
    | v1_relat_1(sK210) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_45384])).

cnf(c_1506,negated_conjecture,
    ( v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f4115])).

cnf(c_1648,plain,
    ( v1_relat_1(sK210) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_1505,negated_conjecture,
    ( v1_funct_1(sK210) ),
    inference(cnf_transformation,[],[f4116])).

cnf(c_1649,plain,
    ( v1_funct_1(sK210) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1505])).

cnf(c_210804,plain,
    ( r1_tarski(X0,k2_relat_1(sK210)) != iProver_top
    | r1_tarski(X0,sK209) = iProver_top
    | r1_tarski(k10_relat_1(sK210,X0),k10_relat_1(sK210,sK208)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_207061,c_1648,c_1649])).

cnf(c_210811,plain,
    ( r1_tarski(sK208,k2_relat_1(sK210)) != iProver_top
    | r1_tarski(sK208,sK209) = iProver_top ),
    inference(superposition,[status(thm)],[c_46367,c_210804])).

cnf(c_206994,plain,
    ( r1_tarski(k10_relat_1(sK210,sK208),k10_relat_1(sK210,X0)) != iProver_top
    | r1_tarski(sK209,X0) = iProver_top
    | r1_tarski(sK209,k2_relat_1(sK210)) != iProver_top
    | v1_funct_1(sK210) != iProver_top
    | v1_relat_1(sK210) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_45384])).

cnf(c_1502,negated_conjecture,
    ( r1_tarski(sK209,k2_relat_1(sK210)) ),
    inference(cnf_transformation,[],[f4119])).

cnf(c_1651,plain,
    ( r1_tarski(sK209,k2_relat_1(sK210)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1502])).

cnf(c_209946,plain,
    ( r1_tarski(sK209,X0) = iProver_top
    | r1_tarski(k10_relat_1(sK210,sK208),k10_relat_1(sK210,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_206994,c_1648,c_1649,c_1651])).

cnf(c_209947,plain,
    ( r1_tarski(k10_relat_1(sK210,sK208),k10_relat_1(sK210,X0)) != iProver_top
    | r1_tarski(sK209,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_209946])).

cnf(c_209954,plain,
    ( r1_tarski(sK209,sK208) = iProver_top ),
    inference(superposition,[status(thm)],[c_46367,c_209947])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f2668])).

cnf(c_59587,plain,
    ( ~ r1_tarski(sK209,sK208)
    | ~ r1_tarski(sK208,sK209)
    | sK208 = sK209 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_59588,plain,
    ( sK208 = sK209
    | r1_tarski(sK209,sK208) != iProver_top
    | r1_tarski(sK208,sK209) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59587])).

cnf(c_1501,negated_conjecture,
    ( sK208 != sK209 ),
    inference(cnf_transformation,[],[f4120])).

cnf(c_1503,negated_conjecture,
    ( r1_tarski(sK208,k2_relat_1(sK210)) ),
    inference(cnf_transformation,[],[f4118])).

cnf(c_1650,plain,
    ( r1_tarski(sK208,k2_relat_1(sK210)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1503])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_210811,c_209954,c_59588,c_1501,c_1650])).

%------------------------------------------------------------------------------
