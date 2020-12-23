%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1092+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:52 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   35 (  61 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 200 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
         => v1_finset_1(k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      & v1_finset_1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      & v1_finset_1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0] :
        ( ~ v1_finset_1(k2_relat_1(X0))
        & v1_finset_1(k1_relat_1(X0))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v1_finset_1(k2_relat_1(sK0))
      & v1_finset_1(k1_relat_1(sK0))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ~ v1_finset_1(k2_relat_1(sK0))
    & v1_finset_1(k1_relat_1(sK0))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    ~ v1_finset_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,plain,(
    v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_89,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_90,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_89])).

cnf(c_121,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_90])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k9_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_4,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_68,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k9_relat_1(X0,X1))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_69,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_finset_1(X0)
    | v1_finset_1(k9_relat_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_68])).

cnf(c_73,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k9_relat_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_69,c_5])).

cnf(c_122,plain,
    ( ~ v1_finset_1(X0_35)
    | v1_finset_1(k9_relat_1(sK0,X0_35)) ),
    inference(subtyping,[status(esa)],[c_73])).

cnf(c_195,plain,
    ( v1_finset_1(X0_35) != iProver_top
    | v1_finset_1(k9_relat_1(sK0,X0_35)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122])).

cnf(c_295,plain,
    ( v1_finset_1(k2_relat_1(sK0)) = iProver_top
    | v1_finset_1(k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_121,c_195])).

cnf(c_2,negated_conjecture,
    ( ~ v1_finset_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,plain,
    ( v1_finset_1(k2_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,negated_conjecture,
    ( v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_8,plain,
    ( v1_finset_1(k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_295,c_9,c_8])).


%------------------------------------------------------------------------------
