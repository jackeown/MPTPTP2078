%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0645+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 15.59s
% Output     : CNFRefutation 15.59s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    7
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f939,conjecture,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f940,negated_conjecture,(
    ~ ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f939])).

fof(f1750,plain,(
    ? [X0] : ~ v2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f940])).

fof(f2310,plain,
    ( ? [X0] : ~ v2_funct_1(k6_relat_1(X0))
   => ~ v2_funct_1(k6_relat_1(sK201)) ),
    introduced(choice_axiom,[])).

fof(f2311,plain,(
    ~ v2_funct_1(k6_relat_1(sK201)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK201])],[f1750,f2310])).

fof(f3824,plain,(
    ~ v2_funct_1(k6_relat_1(sK201)) ),
    inference(cnf_transformation,[],[f2311])).

fof(f901,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3700,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f901])).

cnf(c_1494,negated_conjecture,
    ( ~ v2_funct_1(k6_relat_1(sK201)) ),
    inference(cnf_transformation,[],[f3824])).

cnf(c_41052,plain,
    ( v2_funct_1(k6_relat_1(sK201)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1494])).

cnf(c_1369,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3700])).

cnf(c_41148,plain,
    ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_42218,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_41052,c_41148])).

%------------------------------------------------------------------------------
