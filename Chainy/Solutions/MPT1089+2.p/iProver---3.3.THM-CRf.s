%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1089+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 42.83s
% Output     : CNFRefutation 42.83s
% Verified   : 
% Statistics : Number of formulae       :   26 (  44 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 152 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1713,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3640,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1713])).

fof(f3641,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3640])).

fof(f8385,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3641])).

fof(f1720,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_finset_1(X0)
       => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1721,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v1_finset_1(X0)
         => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1720])).

fof(f3650,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k9_relat_1(X1,X0))
      & v1_finset_1(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1721])).

fof(f3651,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k9_relat_1(X1,X0))
      & v1_finset_1(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f3650])).

fof(f5092,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k9_relat_1(X1,X0))
        & v1_finset_1(X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(k9_relat_1(sK602,sK601))
      & v1_finset_1(sK601)
      & v1_funct_1(sK602)
      & v1_relat_1(sK602) ) ),
    introduced(choice_axiom,[])).

fof(f5093,plain,
    ( ~ v1_finset_1(k9_relat_1(sK602,sK601))
    & v1_finset_1(sK601)
    & v1_funct_1(sK602)
    & v1_relat_1(sK602) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK601,sK602])],[f3651,f5092])).

fof(f8396,plain,(
    ~ v1_finset_1(k9_relat_1(sK602,sK601)) ),
    inference(cnf_transformation,[],[f5093])).

fof(f8395,plain,(
    v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f5093])).

fof(f8394,plain,(
    v1_funct_1(sK602) ),
    inference(cnf_transformation,[],[f5093])).

fof(f8393,plain,(
    v1_relat_1(sK602) ),
    inference(cnf_transformation,[],[f5093])).

cnf(c_3265,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k9_relat_1(X1,X0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f8385])).

cnf(c_94683,plain,
    ( v1_finset_1(X0) != iProver_top
    | v1_finset_1(k9_relat_1(X1,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3265])).

cnf(c_3273,negated_conjecture,
    ( ~ v1_finset_1(k9_relat_1(sK602,sK601)) ),
    inference(cnf_transformation,[],[f8396])).

cnf(c_94677,plain,
    ( v1_finset_1(k9_relat_1(sK602,sK601)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3273])).

cnf(c_124488,plain,
    ( v1_finset_1(sK601) != iProver_top
    | v1_funct_1(sK602) != iProver_top
    | v1_relat_1(sK602) != iProver_top ),
    inference(superposition,[status(thm)],[c_94683,c_94677])).

cnf(c_3274,negated_conjecture,
    ( v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f8395])).

cnf(c_3279,plain,
    ( v1_finset_1(sK601) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3274])).

cnf(c_3275,negated_conjecture,
    ( v1_funct_1(sK602) ),
    inference(cnf_transformation,[],[f8394])).

cnf(c_3278,plain,
    ( v1_funct_1(sK602) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3275])).

cnf(c_3276,negated_conjecture,
    ( v1_relat_1(sK602) ),
    inference(cnf_transformation,[],[f8393])).

cnf(c_3277,plain,
    ( v1_relat_1(sK602) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3276])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124488,c_3279,c_3278,c_3277])).

%------------------------------------------------------------------------------
