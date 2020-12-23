%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0936+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 23.16s
% Output     : CNFRefutation 23.16s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1416,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1417,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f1416])).

fof(f2853,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f1417])).

fof(f3964,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK458) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK458,sK459,sK460)))) ),
    introduced(choice_axiom,[])).

fof(f3965,plain,(
    k1_tarski(sK458) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK458,sK459,sK460)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK458,sK459,sK460])],[f2853,f3964])).

fof(f6518,plain,(
    k1_tarski(sK458) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK458,sK459,sK460)))) ),
    inference(cnf_transformation,[],[f3965])).

fof(f1280,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6174,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1280])).

fof(f7468,plain,(
    k1_tarski(sK458) != k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)))) ),
    inference(definition_unfolding,[],[f6518,f6174])).

fof(f827,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2092,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f827])).

fof(f2093,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2092])).

fof(f5240,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2093])).

fof(f7660,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f5240])).

fof(f695,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5085,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f695])).

cnf(c_2527,negated_conjecture,
    ( k1_tarski(sK458) != k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)))) ),
    inference(cnf_transformation,[],[f7468])).

cnf(c_1259,plain,
    ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
    | k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7660])).

cnf(c_1103,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f5085])).

cnf(c_20460,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_1103])).

cnf(c_74378,plain,
    ( k1_tarski(sK458) != k1_tarski(sK458) ),
    inference(demodulation,[status(thm)],[c_2527,c_20460])).

cnf(c_74379,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_74378])).

%------------------------------------------------------------------------------
