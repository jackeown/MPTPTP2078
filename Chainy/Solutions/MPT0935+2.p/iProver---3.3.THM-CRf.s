%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0935+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 27.11s
% Output     : CNFRefutation 27.11s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 113 expanded)
%              Number of clauses        :   13 (  21 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 129 expanded)
%              Number of equality atoms :   50 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1415,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) = k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1416,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) = k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    inference(negated_conjecture,[],[f1415])).

fof(f2852,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    inference(ennf_transformation,[],[f1416])).

fof(f3963,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5))))
   => k2_tarski(sK458,sK461) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK458,sK459,sK460),k3_mcart_1(sK461,sK462,sK463)))) ),
    introduced(choice_axiom,[])).

fof(f3964,plain,(
    k2_tarski(sK458,sK461) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK458,sK459,sK460),k3_mcart_1(sK461,sK462,sK463)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK458,sK459,sK460,sK461,sK462,sK463])],[f2852,f3963])).

fof(f6516,plain,(
    k2_tarski(sK458,sK461) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK458,sK459,sK460),k3_mcart_1(sK461,sK462,sK463)))) ),
    inference(cnf_transformation,[],[f3964])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4278,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4182,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4122,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f6520,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f4182,f4122])).

fof(f6521,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f4278,f6520])).

fof(f1280,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6173,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1280])).

fof(f7465,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK458),k1_tarski(sK461)),k4_xboole_0(k1_tarski(sK458),k4_xboole_0(k1_tarski(sK458),k1_tarski(sK461)))) != k1_relat_1(k1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k1_tarski(k4_tarski(k4_tarski(sK461,sK462),sK463))),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k1_tarski(k4_tarski(k4_tarski(sK461,sK462),sK463))))))) ),
    inference(definition_unfolding,[],[f6516,f6521,f6521,f6173,f6173])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4179,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3971,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4186,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f6669,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f4186,f6520])).

fof(f828,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_tarski(X1,X3) = k2_relat_1(X4)
          & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2093,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f828])).

fof(f2094,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f2093])).

fof(f5241,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f2094])).

fof(f7085,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))) = k1_relat_1(X4)
      | k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(definition_unfolding,[],[f5241,f6521,f6521])).

fof(f7659,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))) = k1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))))
      | ~ v1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))))) ) ),
    inference(equality_resolution,[],[f7085])).

fof(f697,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5086,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f697])).

fof(f7033,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))))) ),
    inference(definition_unfolding,[],[f5086,f6521])).

cnf(c_2526,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK458),k1_tarski(sK461)),k4_xboole_0(k1_tarski(sK458),k4_xboole_0(k1_tarski(sK458),k1_tarski(sK461)))) != k1_relat_1(k1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k1_tarski(k4_tarski(k4_tarski(sK461,sK462),sK463))),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k1_tarski(k4_tarski(k4_tarski(sK461,sK462),sK463))))))) ),
    inference(cnf_transformation,[],[f7465])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4179])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3971])).

cnf(c_35240,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k5_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k5_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK461,sK462),sK463)),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK458,sK459),sK460)),k1_tarski(k4_tarski(k4_tarski(sK461,sK462),sK463)))))))) != k5_xboole_0(k1_tarski(sK458),k5_xboole_0(k1_tarski(sK461),k4_xboole_0(k1_tarski(sK458),k4_xboole_0(k1_tarski(sK458),k1_tarski(sK461))))) ),
    inference(theory_normalisation,[status(thm)],[c_2526,c_211,c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6669])).

cnf(c_35507,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_1261,plain,
    ( ~ v1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))))
    | k1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))) ),
    inference(cnf_transformation,[],[f7659])).

cnf(c_1105,plain,
    ( v1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))))) ),
    inference(cnf_transformation,[],[f7033])).

cnf(c_22820,plain,
    ( k1_relat_1(k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1261,c_1105])).

cnf(c_35236,plain,
    ( k1_relat_1(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k5_xboole_0(k1_tarski(k4_tarski(X2,X3)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))))) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))))) ),
    inference(theory_normalisation,[status(thm)],[c_22820,c_211,c_7])).

cnf(c_83582,plain,
    ( k1_relat_1(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X2,X3)),k1_tarski(k4_tarski(X0,X1))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X2),k1_tarski(X0))) ),
    inference(demodulation,[status(thm)],[c_35236,c_35507])).

cnf(c_86038,plain,
    ( k5_xboole_0(k1_tarski(sK458),k4_xboole_0(k1_tarski(sK461),k1_tarski(sK458))) != k5_xboole_0(k1_tarski(sK458),k4_xboole_0(k1_tarski(sK461),k1_tarski(sK458))) ),
    inference(demodulation,[status(thm)],[c_35240,c_35507,c_83582])).

cnf(c_86039,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_86038])).

%------------------------------------------------------------------------------
