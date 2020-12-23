%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0566+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:36 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   24 (  36 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   42 (  68 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f13,plain,(
    ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_2,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_71,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_72,plain,
    ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_71])).

cnf(c_83,plain,
    ( k10_relat_1(sK1,X0) != k10_relat_1(sK1,sK0)
    | k10_relat_1(sK1,k2_relat_1(sK1)) != k1_relat_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_72])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_7,plain,
    ( ~ v1_relat_1(sK1)
    | k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_85,plain,
    ( k10_relat_1(sK1,X0) != k10_relat_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_83,c_3,c_7])).

cnf(c_97,plain,
    ( k10_relat_1(sK1,X0_37) != k10_relat_1(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_85])).

cnf(c_104,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_97])).


%------------------------------------------------------------------------------
