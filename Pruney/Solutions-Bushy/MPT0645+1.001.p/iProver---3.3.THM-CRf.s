%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0645+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:48 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    6
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f8,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,conjecture,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0] : ~ v2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,
    ( ? [X0] : ~ v2_funct_1(k6_relat_1(X0))
   => ~ v2_funct_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f9,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_0,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_4,plain,
    ( v2_funct_1(k6_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,negated_conjecture,
    ( ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4,c_1])).


%------------------------------------------------------------------------------
