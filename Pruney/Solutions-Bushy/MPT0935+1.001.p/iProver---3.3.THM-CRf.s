%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:27 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  40 expanded)
%              Number of equality atoms :   28 (  30 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) = k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) = k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5))))
   => k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).

fof(f15,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK3,sK4),sK5)))) ),
    inference(definition_unfolding,[],[f15,f11,f11])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_tarski(X1,X3) = k2_relat_1(X4)
          & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_3,negated_conjecture,
    ( k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK3,sK4),sK5)))) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_47,negated_conjecture,
    ( k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK3,sK4),sK5)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,plain,
    ( ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
    | k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) = k2_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_20,plain,
    ( k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) = k2_tarski(X0,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_0])).

cnf(c_46,plain,
    ( k1_relat_1(k2_tarski(k4_tarski(X0_40,X1_40),k4_tarski(X2_40,X3_40))) = k2_tarski(X0_40,X2_40) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_57,plain,
    ( k2_tarski(sK0,sK3) != k2_tarski(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_47,c_46])).

cnf(c_58,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_57])).


%------------------------------------------------------------------------------
