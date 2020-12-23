%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1093+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:52 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   47 (  87 expanded)
%              Number of clauses        :   28 (  30 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 353 expanded)
%              Number of equality atoms :   34 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v1_finset_1(k10_relat_1(X1,X0))
          & r1_tarski(X0,k2_relat_1(X1)) )
       => v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v1_finset_1(k10_relat_1(X1,X0))
            & r1_tarski(X0,k2_relat_1(X1)) )
         => v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(k10_relat_1(X1,X0))
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(sK0)
      & v1_finset_1(k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ v1_finset_1(sK0)
    & v1_finset_1(k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f16,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    v1_finset_1(k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_166,plain,
    ( X0_37 != X1_37
    | X2_37 != X1_37
    | X2_37 = X0_37 ),
    theory(equality)).

cnf(c_288,plain,
    ( X0_37 != X1_37
    | X0_37 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != X1_37 ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_289,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0
    | sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_168,plain,
    ( ~ v1_finset_1(X0_37)
    | v1_finset_1(X1_37)
    | X1_37 != X0_37 ),
    theory(equality)).

cnf(c_264,plain,
    ( v1_finset_1(X0_37)
    | ~ v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | X0_37 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_269,plain,
    ( ~ v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | v1_finset_1(sK0)
    | sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k9_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_111,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k9_relat_1(X0,X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_112,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_finset_1(X0)
    | v1_finset_1(k9_relat_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_116,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k9_relat_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_112,c_6])).

cnf(c_161,plain,
    ( ~ v1_finset_1(X0_37)
    | v1_finset_1(k9_relat_1(sK1,X0_37)) ),
    inference(subtyping,[status(esa)],[c_116])).

cnf(c_252,plain,
    ( ~ v1_finset_1(k10_relat_1(sK1,sK0))
    | v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_77,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | k2_relat_1(X0) != k2_relat_1(sK1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_78,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,k10_relat_1(X0,sK0)) = sK0
    | k2_relat_1(X0) != k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_77])).

cnf(c_100,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k10_relat_1(X0,sK0)) = sK0
    | k2_relat_1(X0) != k2_relat_1(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_78,c_5])).

cnf(c_101,plain,
    ( ~ v1_relat_1(sK1)
    | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0
    | k2_relat_1(sK1) != k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_100])).

cnf(c_103,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0
    | k2_relat_1(sK1) != k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_101,c_6])).

cnf(c_138,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_103])).

cnf(c_160,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0 ),
    inference(subtyping,[status(esa)],[c_138])).

cnf(c_165,plain,
    ( X0_37 = X0_37 ),
    theory(equality)).

cnf(c_174,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_2,negated_conjecture,
    ( ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,negated_conjecture,
    ( v1_finset_1(k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_289,c_269,c_252,c_160,c_174,c_2,c_3])).


%------------------------------------------------------------------------------
