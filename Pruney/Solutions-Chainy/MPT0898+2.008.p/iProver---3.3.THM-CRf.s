%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:44 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   76 (1287 expanded)
%              Number of clauses        :   51 ( 460 expanded)
%              Number of leaves         :    8 ( 322 expanded)
%              Depth                    :   24
%              Number of atoms          :  191 (3457 expanded)
%              Number of equality atoms :  190 (3456 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f19,f15])).

fof(f30,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2) ),
    inference(equality_resolution,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f28,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f17,f15])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_111,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) = X1
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_162,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | k2_zfmisc_1(X2,k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k2_relat_1(k1_xboole_0)) = X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_111,c_1])).

cnf(c_6,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_18,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_26,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_58,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_29,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_66,plain,
    ( sK1 != X0
    | sK1 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_68,plain,
    ( sK1 = sK0
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_17,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_84,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_7,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_113,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) = k1_xboole_0
    | k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_30,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_31,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_42,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_57,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_330,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_386,plain,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_113,c_31,c_33,c_330])).

cnf(c_401,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k1_xboole_0
    | sK1 = sK0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_386,c_0])).

cnf(c_59,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_71,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_72,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,sK0),X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_145,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,sK0),sK0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_440,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_1183,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_6,c_58,c_72,c_84,c_440])).

cnf(c_1185,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1183,c_7])).

cnf(c_1190,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1185,c_3])).

cnf(c_1320,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k1_relat_1(k1_xboole_0)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1190,c_1])).

cnf(c_2691,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k1_relat_1(k1_xboole_0)
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_72,c_84,c_440])).

cnf(c_2703,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2691,c_5])).

cnf(c_1323,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1190,c_5])).

cnf(c_2697,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK0) = k1_relat_1(k1_xboole_0)
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1323,c_2691])).

cnf(c_81,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_3])).

cnf(c_2713,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2697,c_81])).

cnf(c_2718,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2703,c_2713])).

cnf(c_178,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),X0) != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) = k1_xboole_0
    | sK1 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_560,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),X0) != k1_xboole_0
    | sK1 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_178,c_31,c_33,c_330])).

cnf(c_2728,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0),X0) != k1_xboole_0
    | sK1 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_2718,c_560])).

cnf(c_2745,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2728,c_3])).

cnf(c_2746,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2745])).

cnf(c_2992,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_162,c_6,c_58,c_68,c_84,c_2703,c_2713,c_2746])).

cnf(c_2736,plain,
    ( sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2718,c_6])).

cnf(c_3002,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2992,c_2736])).

cnf(c_3003,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3002])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.48/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.03  
% 2.48/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/1.03  
% 2.48/1.03  ------  iProver source info
% 2.48/1.03  
% 2.48/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.48/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/1.03  git: non_committed_changes: false
% 2.48/1.03  git: last_make_outside_of_git: false
% 2.48/1.03  
% 2.48/1.03  ------ 
% 2.48/1.03  
% 2.48/1.03  ------ Input Options
% 2.48/1.03  
% 2.48/1.03  --out_options                           all
% 2.48/1.03  --tptp_safe_out                         true
% 2.48/1.03  --problem_path                          ""
% 2.48/1.03  --include_path                          ""
% 2.48/1.03  --clausifier                            res/vclausify_rel
% 2.48/1.03  --clausifier_options                    ""
% 2.48/1.03  --stdin                                 false
% 2.48/1.03  --stats_out                             all
% 2.48/1.03  
% 2.48/1.03  ------ General Options
% 2.48/1.03  
% 2.48/1.03  --fof                                   false
% 2.48/1.03  --time_out_real                         305.
% 2.48/1.03  --time_out_virtual                      -1.
% 2.48/1.03  --symbol_type_check                     false
% 2.48/1.03  --clausify_out                          false
% 2.48/1.03  --sig_cnt_out                           false
% 2.48/1.03  --trig_cnt_out                          false
% 2.48/1.03  --trig_cnt_out_tolerance                1.
% 2.48/1.03  --trig_cnt_out_sk_spl                   false
% 2.48/1.03  --abstr_cl_out                          false
% 2.48/1.03  
% 2.48/1.03  ------ Global Options
% 2.48/1.03  
% 2.48/1.03  --schedule                              default
% 2.48/1.03  --add_important_lit                     false
% 2.48/1.03  --prop_solver_per_cl                    1000
% 2.48/1.03  --min_unsat_core                        false
% 2.48/1.03  --soft_assumptions                      false
% 2.48/1.03  --soft_lemma_size                       3
% 2.48/1.03  --prop_impl_unit_size                   0
% 2.48/1.03  --prop_impl_unit                        []
% 2.48/1.03  --share_sel_clauses                     true
% 2.48/1.03  --reset_solvers                         false
% 2.48/1.03  --bc_imp_inh                            [conj_cone]
% 2.48/1.03  --conj_cone_tolerance                   3.
% 2.48/1.03  --extra_neg_conj                        none
% 2.48/1.03  --large_theory_mode                     true
% 2.48/1.03  --prolific_symb_bound                   200
% 2.48/1.03  --lt_threshold                          2000
% 2.48/1.03  --clause_weak_htbl                      true
% 2.48/1.03  --gc_record_bc_elim                     false
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing Options
% 2.48/1.03  
% 2.48/1.03  --preprocessing_flag                    true
% 2.48/1.03  --time_out_prep_mult                    0.1
% 2.48/1.03  --splitting_mode                        input
% 2.48/1.03  --splitting_grd                         true
% 2.48/1.03  --splitting_cvd                         false
% 2.48/1.03  --splitting_cvd_svl                     false
% 2.48/1.03  --splitting_nvd                         32
% 2.48/1.03  --sub_typing                            true
% 2.48/1.03  --prep_gs_sim                           true
% 2.48/1.03  --prep_unflatten                        true
% 2.48/1.03  --prep_res_sim                          true
% 2.48/1.03  --prep_upred                            true
% 2.48/1.03  --prep_sem_filter                       exhaustive
% 2.48/1.03  --prep_sem_filter_out                   false
% 2.48/1.03  --pred_elim                             true
% 2.48/1.03  --res_sim_input                         true
% 2.48/1.03  --eq_ax_congr_red                       true
% 2.48/1.03  --pure_diseq_elim                       true
% 2.48/1.03  --brand_transform                       false
% 2.48/1.03  --non_eq_to_eq                          false
% 2.48/1.03  --prep_def_merge                        true
% 2.48/1.03  --prep_def_merge_prop_impl              false
% 2.48/1.03  --prep_def_merge_mbd                    true
% 2.48/1.03  --prep_def_merge_tr_red                 false
% 2.48/1.03  --prep_def_merge_tr_cl                  false
% 2.48/1.03  --smt_preprocessing                     true
% 2.48/1.03  --smt_ac_axioms                         fast
% 2.48/1.03  --preprocessed_out                      false
% 2.48/1.03  --preprocessed_stats                    false
% 2.48/1.03  
% 2.48/1.03  ------ Abstraction refinement Options
% 2.48/1.03  
% 2.48/1.03  --abstr_ref                             []
% 2.48/1.03  --abstr_ref_prep                        false
% 2.48/1.03  --abstr_ref_until_sat                   false
% 2.48/1.03  --abstr_ref_sig_restrict                funpre
% 2.48/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.03  --abstr_ref_under                       []
% 2.48/1.03  
% 2.48/1.03  ------ SAT Options
% 2.48/1.03  
% 2.48/1.03  --sat_mode                              false
% 2.48/1.03  --sat_fm_restart_options                ""
% 2.48/1.03  --sat_gr_def                            false
% 2.48/1.03  --sat_epr_types                         true
% 2.48/1.03  --sat_non_cyclic_types                  false
% 2.48/1.03  --sat_finite_models                     false
% 2.48/1.03  --sat_fm_lemmas                         false
% 2.48/1.03  --sat_fm_prep                           false
% 2.48/1.03  --sat_fm_uc_incr                        true
% 2.48/1.03  --sat_out_model                         small
% 2.48/1.03  --sat_out_clauses                       false
% 2.48/1.03  
% 2.48/1.03  ------ QBF Options
% 2.48/1.03  
% 2.48/1.03  --qbf_mode                              false
% 2.48/1.03  --qbf_elim_univ                         false
% 2.48/1.03  --qbf_dom_inst                          none
% 2.48/1.03  --qbf_dom_pre_inst                      false
% 2.48/1.03  --qbf_sk_in                             false
% 2.48/1.03  --qbf_pred_elim                         true
% 2.48/1.03  --qbf_split                             512
% 2.48/1.03  
% 2.48/1.03  ------ BMC1 Options
% 2.48/1.03  
% 2.48/1.03  --bmc1_incremental                      false
% 2.48/1.03  --bmc1_axioms                           reachable_all
% 2.48/1.03  --bmc1_min_bound                        0
% 2.48/1.03  --bmc1_max_bound                        -1
% 2.48/1.03  --bmc1_max_bound_default                -1
% 2.48/1.03  --bmc1_symbol_reachability              true
% 2.48/1.03  --bmc1_property_lemmas                  false
% 2.48/1.03  --bmc1_k_induction                      false
% 2.48/1.03  --bmc1_non_equiv_states                 false
% 2.48/1.03  --bmc1_deadlock                         false
% 2.48/1.03  --bmc1_ucm                              false
% 2.48/1.03  --bmc1_add_unsat_core                   none
% 2.48/1.03  --bmc1_unsat_core_children              false
% 2.48/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.03  --bmc1_out_stat                         full
% 2.48/1.03  --bmc1_ground_init                      false
% 2.48/1.03  --bmc1_pre_inst_next_state              false
% 2.48/1.03  --bmc1_pre_inst_state                   false
% 2.48/1.03  --bmc1_pre_inst_reach_state             false
% 2.48/1.03  --bmc1_out_unsat_core                   false
% 2.48/1.03  --bmc1_aig_witness_out                  false
% 2.48/1.03  --bmc1_verbose                          false
% 2.48/1.03  --bmc1_dump_clauses_tptp                false
% 2.48/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.03  --bmc1_dump_file                        -
% 2.48/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.03  --bmc1_ucm_extend_mode                  1
% 2.48/1.03  --bmc1_ucm_init_mode                    2
% 2.48/1.03  --bmc1_ucm_cone_mode                    none
% 2.48/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.03  --bmc1_ucm_relax_model                  4
% 2.48/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.03  --bmc1_ucm_layered_model                none
% 2.48/1.03  --bmc1_ucm_max_lemma_size               10
% 2.48/1.03  
% 2.48/1.03  ------ AIG Options
% 2.48/1.03  
% 2.48/1.03  --aig_mode                              false
% 2.48/1.03  
% 2.48/1.03  ------ Instantiation Options
% 2.48/1.03  
% 2.48/1.03  --instantiation_flag                    true
% 2.48/1.03  --inst_sos_flag                         true
% 2.48/1.03  --inst_sos_phase                        true
% 2.48/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.03  --inst_lit_sel_side                     num_symb
% 2.48/1.03  --inst_solver_per_active                1400
% 2.48/1.03  --inst_solver_calls_frac                1.
% 2.48/1.03  --inst_passive_queue_type               priority_queues
% 2.48/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.03  --inst_passive_queues_freq              [25;2]
% 2.48/1.03  --inst_dismatching                      true
% 2.48/1.03  --inst_eager_unprocessed_to_passive     true
% 2.48/1.03  --inst_prop_sim_given                   true
% 2.48/1.03  --inst_prop_sim_new                     false
% 2.48/1.03  --inst_subs_new                         false
% 2.48/1.03  --inst_eq_res_simp                      false
% 2.48/1.03  --inst_subs_given                       false
% 2.48/1.03  --inst_orphan_elimination               true
% 2.48/1.03  --inst_learning_loop_flag               true
% 2.48/1.03  --inst_learning_start                   3000
% 2.48/1.03  --inst_learning_factor                  2
% 2.48/1.03  --inst_start_prop_sim_after_learn       3
% 2.48/1.03  --inst_sel_renew                        solver
% 2.48/1.03  --inst_lit_activity_flag                true
% 2.48/1.03  --inst_restr_to_given                   false
% 2.48/1.03  --inst_activity_threshold               500
% 2.48/1.03  --inst_out_proof                        true
% 2.48/1.03  
% 2.48/1.03  ------ Resolution Options
% 2.48/1.03  
% 2.48/1.03  --resolution_flag                       true
% 2.48/1.03  --res_lit_sel                           adaptive
% 2.48/1.03  --res_lit_sel_side                      none
% 2.48/1.03  --res_ordering                          kbo
% 2.48/1.03  --res_to_prop_solver                    active
% 2.48/1.03  --res_prop_simpl_new                    false
% 2.48/1.03  --res_prop_simpl_given                  true
% 2.48/1.03  --res_passive_queue_type                priority_queues
% 2.48/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.03  --res_passive_queues_freq               [15;5]
% 2.48/1.03  --res_forward_subs                      full
% 2.48/1.03  --res_backward_subs                     full
% 2.48/1.03  --res_forward_subs_resolution           true
% 2.48/1.03  --res_backward_subs_resolution          true
% 2.48/1.03  --res_orphan_elimination                true
% 2.48/1.03  --res_time_limit                        2.
% 2.48/1.03  --res_out_proof                         true
% 2.48/1.03  
% 2.48/1.03  ------ Superposition Options
% 2.48/1.03  
% 2.48/1.03  --superposition_flag                    true
% 2.48/1.03  --sup_passive_queue_type                priority_queues
% 2.48/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.03  --demod_completeness_check              fast
% 2.48/1.03  --demod_use_ground                      true
% 2.48/1.03  --sup_to_prop_solver                    passive
% 2.48/1.03  --sup_prop_simpl_new                    true
% 2.48/1.03  --sup_prop_simpl_given                  true
% 2.48/1.03  --sup_fun_splitting                     true
% 2.48/1.03  --sup_smt_interval                      50000
% 2.48/1.03  
% 2.48/1.03  ------ Superposition Simplification Setup
% 2.48/1.03  
% 2.48/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.48/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.48/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.48/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.48/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.48/1.03  --sup_immed_triv                        [TrivRules]
% 2.48/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.03  --sup_immed_bw_main                     []
% 2.48/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.48/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.03  --sup_input_bw                          []
% 2.48/1.03  
% 2.48/1.03  ------ Combination Options
% 2.48/1.03  
% 2.48/1.03  --comb_res_mult                         3
% 2.48/1.03  --comb_sup_mult                         2
% 2.48/1.03  --comb_inst_mult                        10
% 2.48/1.03  
% 2.48/1.03  ------ Debug Options
% 2.48/1.03  
% 2.48/1.03  --dbg_backtrace                         false
% 2.48/1.03  --dbg_dump_prop_clauses                 false
% 2.48/1.03  --dbg_dump_prop_clauses_file            -
% 2.48/1.03  --dbg_out_stat                          false
% 2.48/1.03  ------ Parsing...
% 2.48/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.48/1.03  ------ Proving...
% 2.48/1.03  ------ Problem Properties 
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  clauses                                 8
% 2.48/1.03  conjectures                             2
% 2.48/1.03  EPR                                     1
% 2.48/1.03  Horn                                    5
% 2.48/1.03  unary                                   5
% 2.48/1.03  binary                                  0
% 2.48/1.03  lits                                    15
% 2.48/1.03  lits eq                                 15
% 2.48/1.03  fd_pure                                 0
% 2.48/1.03  fd_pseudo                               0
% 2.48/1.03  fd_cond                                 1
% 2.48/1.03  fd_pseudo_cond                          0
% 2.48/1.03  AC symbols                              0
% 2.48/1.03  
% 2.48/1.03  ------ Schedule dynamic 5 is on 
% 2.48/1.03  
% 2.48/1.03  ------ pure equality problem: resolution off 
% 2.48/1.03  
% 2.48/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  ------ 
% 2.48/1.03  Current options:
% 2.48/1.03  ------ 
% 2.48/1.03  
% 2.48/1.03  ------ Input Options
% 2.48/1.03  
% 2.48/1.03  --out_options                           all
% 2.48/1.03  --tptp_safe_out                         true
% 2.48/1.03  --problem_path                          ""
% 2.48/1.03  --include_path                          ""
% 2.48/1.03  --clausifier                            res/vclausify_rel
% 2.48/1.03  --clausifier_options                    ""
% 2.48/1.03  --stdin                                 false
% 2.48/1.03  --stats_out                             all
% 2.48/1.03  
% 2.48/1.03  ------ General Options
% 2.48/1.03  
% 2.48/1.03  --fof                                   false
% 2.48/1.03  --time_out_real                         305.
% 2.48/1.03  --time_out_virtual                      -1.
% 2.48/1.03  --symbol_type_check                     false
% 2.48/1.03  --clausify_out                          false
% 2.48/1.03  --sig_cnt_out                           false
% 2.48/1.03  --trig_cnt_out                          false
% 2.48/1.03  --trig_cnt_out_tolerance                1.
% 2.48/1.03  --trig_cnt_out_sk_spl                   false
% 2.48/1.03  --abstr_cl_out                          false
% 2.48/1.03  
% 2.48/1.03  ------ Global Options
% 2.48/1.03  
% 2.48/1.03  --schedule                              default
% 2.48/1.03  --add_important_lit                     false
% 2.48/1.03  --prop_solver_per_cl                    1000
% 2.48/1.03  --min_unsat_core                        false
% 2.48/1.03  --soft_assumptions                      false
% 2.48/1.03  --soft_lemma_size                       3
% 2.48/1.03  --prop_impl_unit_size                   0
% 2.48/1.03  --prop_impl_unit                        []
% 2.48/1.03  --share_sel_clauses                     true
% 2.48/1.03  --reset_solvers                         false
% 2.48/1.03  --bc_imp_inh                            [conj_cone]
% 2.48/1.03  --conj_cone_tolerance                   3.
% 2.48/1.03  --extra_neg_conj                        none
% 2.48/1.03  --large_theory_mode                     true
% 2.48/1.03  --prolific_symb_bound                   200
% 2.48/1.03  --lt_threshold                          2000
% 2.48/1.03  --clause_weak_htbl                      true
% 2.48/1.03  --gc_record_bc_elim                     false
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing Options
% 2.48/1.03  
% 2.48/1.03  --preprocessing_flag                    true
% 2.48/1.03  --time_out_prep_mult                    0.1
% 2.48/1.03  --splitting_mode                        input
% 2.48/1.03  --splitting_grd                         true
% 2.48/1.03  --splitting_cvd                         false
% 2.48/1.03  --splitting_cvd_svl                     false
% 2.48/1.03  --splitting_nvd                         32
% 2.48/1.03  --sub_typing                            true
% 2.48/1.03  --prep_gs_sim                           true
% 2.48/1.03  --prep_unflatten                        true
% 2.48/1.03  --prep_res_sim                          true
% 2.48/1.03  --prep_upred                            true
% 2.48/1.03  --prep_sem_filter                       exhaustive
% 2.48/1.03  --prep_sem_filter_out                   false
% 2.48/1.03  --pred_elim                             true
% 2.48/1.03  --res_sim_input                         true
% 2.48/1.03  --eq_ax_congr_red                       true
% 2.48/1.03  --pure_diseq_elim                       true
% 2.48/1.03  --brand_transform                       false
% 2.48/1.03  --non_eq_to_eq                          false
% 2.48/1.03  --prep_def_merge                        true
% 2.48/1.03  --prep_def_merge_prop_impl              false
% 2.48/1.03  --prep_def_merge_mbd                    true
% 2.48/1.03  --prep_def_merge_tr_red                 false
% 2.48/1.03  --prep_def_merge_tr_cl                  false
% 2.48/1.03  --smt_preprocessing                     true
% 2.48/1.03  --smt_ac_axioms                         fast
% 2.48/1.03  --preprocessed_out                      false
% 2.48/1.03  --preprocessed_stats                    false
% 2.48/1.03  
% 2.48/1.03  ------ Abstraction refinement Options
% 2.48/1.03  
% 2.48/1.03  --abstr_ref                             []
% 2.48/1.03  --abstr_ref_prep                        false
% 2.48/1.03  --abstr_ref_until_sat                   false
% 2.48/1.03  --abstr_ref_sig_restrict                funpre
% 2.48/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.03  --abstr_ref_under                       []
% 2.48/1.03  
% 2.48/1.03  ------ SAT Options
% 2.48/1.03  
% 2.48/1.03  --sat_mode                              false
% 2.48/1.03  --sat_fm_restart_options                ""
% 2.48/1.03  --sat_gr_def                            false
% 2.48/1.03  --sat_epr_types                         true
% 2.48/1.03  --sat_non_cyclic_types                  false
% 2.48/1.03  --sat_finite_models                     false
% 2.48/1.03  --sat_fm_lemmas                         false
% 2.48/1.03  --sat_fm_prep                           false
% 2.48/1.03  --sat_fm_uc_incr                        true
% 2.48/1.03  --sat_out_model                         small
% 2.48/1.03  --sat_out_clauses                       false
% 2.48/1.03  
% 2.48/1.03  ------ QBF Options
% 2.48/1.03  
% 2.48/1.03  --qbf_mode                              false
% 2.48/1.03  --qbf_elim_univ                         false
% 2.48/1.03  --qbf_dom_inst                          none
% 2.48/1.03  --qbf_dom_pre_inst                      false
% 2.48/1.03  --qbf_sk_in                             false
% 2.48/1.03  --qbf_pred_elim                         true
% 2.48/1.03  --qbf_split                             512
% 2.48/1.03  
% 2.48/1.03  ------ BMC1 Options
% 2.48/1.03  
% 2.48/1.03  --bmc1_incremental                      false
% 2.48/1.03  --bmc1_axioms                           reachable_all
% 2.48/1.03  --bmc1_min_bound                        0
% 2.48/1.03  --bmc1_max_bound                        -1
% 2.48/1.03  --bmc1_max_bound_default                -1
% 2.48/1.03  --bmc1_symbol_reachability              true
% 2.48/1.03  --bmc1_property_lemmas                  false
% 2.48/1.03  --bmc1_k_induction                      false
% 2.48/1.03  --bmc1_non_equiv_states                 false
% 2.48/1.03  --bmc1_deadlock                         false
% 2.48/1.03  --bmc1_ucm                              false
% 2.48/1.03  --bmc1_add_unsat_core                   none
% 2.48/1.03  --bmc1_unsat_core_children              false
% 2.48/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.03  --bmc1_out_stat                         full
% 2.48/1.03  --bmc1_ground_init                      false
% 2.48/1.03  --bmc1_pre_inst_next_state              false
% 2.48/1.03  --bmc1_pre_inst_state                   false
% 2.48/1.03  --bmc1_pre_inst_reach_state             false
% 2.48/1.03  --bmc1_out_unsat_core                   false
% 2.48/1.03  --bmc1_aig_witness_out                  false
% 2.48/1.03  --bmc1_verbose                          false
% 2.48/1.03  --bmc1_dump_clauses_tptp                false
% 2.48/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.03  --bmc1_dump_file                        -
% 2.48/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.03  --bmc1_ucm_extend_mode                  1
% 2.48/1.03  --bmc1_ucm_init_mode                    2
% 2.48/1.03  --bmc1_ucm_cone_mode                    none
% 2.48/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.03  --bmc1_ucm_relax_model                  4
% 2.48/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.03  --bmc1_ucm_layered_model                none
% 2.48/1.03  --bmc1_ucm_max_lemma_size               10
% 2.48/1.03  
% 2.48/1.03  ------ AIG Options
% 2.48/1.03  
% 2.48/1.03  --aig_mode                              false
% 2.48/1.03  
% 2.48/1.03  ------ Instantiation Options
% 2.48/1.03  
% 2.48/1.03  --instantiation_flag                    true
% 2.48/1.03  --inst_sos_flag                         true
% 2.48/1.03  --inst_sos_phase                        true
% 2.48/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.03  --inst_lit_sel_side                     none
% 2.48/1.03  --inst_solver_per_active                1400
% 2.48/1.03  --inst_solver_calls_frac                1.
% 2.48/1.03  --inst_passive_queue_type               priority_queues
% 2.48/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.03  --inst_passive_queues_freq              [25;2]
% 2.48/1.03  --inst_dismatching                      true
% 2.48/1.03  --inst_eager_unprocessed_to_passive     true
% 2.48/1.03  --inst_prop_sim_given                   true
% 2.48/1.03  --inst_prop_sim_new                     false
% 2.48/1.03  --inst_subs_new                         false
% 2.48/1.03  --inst_eq_res_simp                      false
% 2.48/1.03  --inst_subs_given                       false
% 2.48/1.03  --inst_orphan_elimination               true
% 2.48/1.03  --inst_learning_loop_flag               true
% 2.48/1.03  --inst_learning_start                   3000
% 2.48/1.03  --inst_learning_factor                  2
% 2.48/1.03  --inst_start_prop_sim_after_learn       3
% 2.48/1.03  --inst_sel_renew                        solver
% 2.48/1.03  --inst_lit_activity_flag                true
% 2.48/1.03  --inst_restr_to_given                   false
% 2.48/1.03  --inst_activity_threshold               500
% 2.48/1.03  --inst_out_proof                        true
% 2.48/1.03  
% 2.48/1.03  ------ Resolution Options
% 2.48/1.03  
% 2.48/1.03  --resolution_flag                       false
% 2.48/1.03  --res_lit_sel                           adaptive
% 2.48/1.03  --res_lit_sel_side                      none
% 2.48/1.03  --res_ordering                          kbo
% 2.48/1.03  --res_to_prop_solver                    active
% 2.48/1.03  --res_prop_simpl_new                    false
% 2.48/1.03  --res_prop_simpl_given                  true
% 2.48/1.03  --res_passive_queue_type                priority_queues
% 2.48/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.03  --res_passive_queues_freq               [15;5]
% 2.48/1.03  --res_forward_subs                      full
% 2.48/1.03  --res_backward_subs                     full
% 2.48/1.03  --res_forward_subs_resolution           true
% 2.48/1.03  --res_backward_subs_resolution          true
% 2.48/1.03  --res_orphan_elimination                true
% 2.48/1.03  --res_time_limit                        2.
% 2.48/1.03  --res_out_proof                         true
% 2.48/1.03  
% 2.48/1.03  ------ Superposition Options
% 2.48/1.03  
% 2.48/1.03  --superposition_flag                    true
% 2.48/1.03  --sup_passive_queue_type                priority_queues
% 2.48/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.03  --demod_completeness_check              fast
% 2.48/1.03  --demod_use_ground                      true
% 2.48/1.03  --sup_to_prop_solver                    passive
% 2.48/1.03  --sup_prop_simpl_new                    true
% 2.48/1.03  --sup_prop_simpl_given                  true
% 2.48/1.03  --sup_fun_splitting                     true
% 2.48/1.03  --sup_smt_interval                      50000
% 2.48/1.03  
% 2.48/1.03  ------ Superposition Simplification Setup
% 2.48/1.03  
% 2.48/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.48/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.48/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.48/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.48/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.48/1.03  --sup_immed_triv                        [TrivRules]
% 2.48/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.03  --sup_immed_bw_main                     []
% 2.48/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.48/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.03  --sup_input_bw                          []
% 2.48/1.03  
% 2.48/1.03  ------ Combination Options
% 2.48/1.03  
% 2.48/1.03  --comb_res_mult                         3
% 2.48/1.03  --comb_sup_mult                         2
% 2.48/1.03  --comb_inst_mult                        10
% 2.48/1.03  
% 2.48/1.03  ------ Debug Options
% 2.48/1.03  
% 2.48/1.03  --dbg_backtrace                         false
% 2.48/1.03  --dbg_dump_prop_clauses                 false
% 2.48/1.03  --dbg_dump_prop_clauses_file            -
% 2.48/1.03  --dbg_out_stat                          false
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  ------ Proving...
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  % SZS status Theorem for theBenchmark.p
% 2.48/1.03  
% 2.48/1.03   Resolution empty clause
% 2.48/1.03  
% 2.48/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/1.03  
% 2.48/1.03  fof(f4,axiom,(
% 2.48/1.03    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f9,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.48/1.03    inference(nnf_transformation,[],[f4])).
% 2.48/1.03  
% 2.48/1.03  fof(f10,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.48/1.03    inference(flattening,[],[f9])).
% 2.48/1.03  
% 2.48/1.03  fof(f19,plain,(
% 2.48/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f10])).
% 2.48/1.03  
% 2.48/1.03  fof(f2,axiom,(
% 2.48/1.03    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f15,plain,(
% 2.48/1.03    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f2])).
% 2.48/1.03  
% 2.48/1.03  fof(f25,plain,(
% 2.48/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.48/1.03    inference(definition_unfolding,[],[f19,f15])).
% 2.48/1.03  
% 2.48/1.03  fof(f30,plain,(
% 2.48/1.03    ( ! [X2,X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2)) )),
% 2.48/1.03    inference(equality_resolution,[],[f25])).
% 2.48/1.03  
% 2.48/1.03  fof(f1,axiom,(
% 2.48/1.03    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f7,plain,(
% 2.48/1.03    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.48/1.03    inference(ennf_transformation,[],[f1])).
% 2.48/1.03  
% 2.48/1.03  fof(f14,plain,(
% 2.48/1.03    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.48/1.03    inference(cnf_transformation,[],[f7])).
% 2.48/1.03  
% 2.48/1.03  fof(f13,plain,(
% 2.48/1.03    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.48/1.03    inference(cnf_transformation,[],[f7])).
% 2.48/1.03  
% 2.48/1.03  fof(f5,conjecture,(
% 2.48/1.03    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f6,negated_conjecture,(
% 2.48/1.03    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 2.48/1.03    inference(negated_conjecture,[],[f5])).
% 2.48/1.03  
% 2.48/1.03  fof(f8,plain,(
% 2.48/1.03    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 2.48/1.03    inference(ennf_transformation,[],[f6])).
% 2.48/1.03  
% 2.48/1.03  fof(f11,plain,(
% 2.48/1.03    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f12,plain,(
% 2.48/1.03    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 2.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).
% 2.48/1.03  
% 2.48/1.03  fof(f22,plain,(
% 2.48/1.03    sK0 != sK1),
% 2.48/1.03    inference(cnf_transformation,[],[f12])).
% 2.48/1.03  
% 2.48/1.03  fof(f21,plain,(
% 2.48/1.03    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 2.48/1.03    inference(cnf_transformation,[],[f12])).
% 2.48/1.03  
% 2.48/1.03  fof(f3,axiom,(
% 2.48/1.03    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f16,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f3])).
% 2.48/1.03  
% 2.48/1.03  fof(f23,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.48/1.03    inference(definition_unfolding,[],[f16,f15])).
% 2.48/1.03  
% 2.48/1.03  fof(f28,plain,(
% 2.48/1.03    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 2.48/1.03    inference(definition_unfolding,[],[f21,f23,f23])).
% 2.48/1.03  
% 2.48/1.03  fof(f17,plain,(
% 2.48/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.48/1.03    inference(cnf_transformation,[],[f10])).
% 2.48/1.03  
% 2.48/1.03  fof(f27,plain,(
% 2.48/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.48/1.03    inference(definition_unfolding,[],[f17,f15])).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
% 2.48/1.03      inference(cnf_transformation,[],[f30]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_0,plain,
% 2.48/1.03      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 2.48/1.03      | k1_xboole_0 = X1
% 2.48/1.03      | k1_xboole_0 = X0 ),
% 2.48/1.03      inference(cnf_transformation,[],[f14]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_111,plain,
% 2.48/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
% 2.48/1.03      | k2_relat_1(k1_xboole_0) = X1
% 2.48/1.03      | k1_xboole_0 = X1 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1,plain,
% 2.48/1.03      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 2.48/1.03      | k1_xboole_0 = X1
% 2.48/1.03      | k1_xboole_0 = X0 ),
% 2.48/1.03      inference(cnf_transformation,[],[f13]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_162,plain,
% 2.48/1.03      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 2.48/1.03      | k2_zfmisc_1(X2,k1_xboole_0) = k1_xboole_0
% 2.48/1.03      | k1_relat_1(k2_relat_1(k1_xboole_0)) = X0
% 2.48/1.03      | k1_xboole_0 = X0
% 2.48/1.03      | k1_xboole_0 = X1 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_111,c_1]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_6,negated_conjecture,
% 2.48/1.03      ( sK0 != sK1 ),
% 2.48/1.03      inference(cnf_transformation,[],[f22]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_18,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_26,plain,
% 2.48/1.03      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_58,plain,
% 2.48/1.03      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_26]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_29,plain,
% 2.48/1.03      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_66,plain,
% 2.48/1.03      ( sK1 != X0 | sK1 = sK0 | sK0 != X0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_29]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_68,plain,
% 2.48/1.03      ( sK1 = sK0 | sK1 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_66]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_17,plain,( X0 = X0 ),theory(equality) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_84,plain,( sK0 = sK0 ),inference(instantiation,[status(thm)],[c_17]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_7,negated_conjecture,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f28]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_113,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) = k1_xboole_0
% 2.48/1.03      | k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) = sK1
% 2.48/1.03      | sK1 = k1_xboole_0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_30,plain,
% 2.48/1.03      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_29]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_31,plain,
% 2.48/1.03      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_30]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_33,plain,( sK1 = sK1 ),inference(instantiation,[status(thm)],[c_17]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_5,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = X1
% 2.48/1.03      | k1_xboole_0 = X0
% 2.48/1.03      | k1_xboole_0 = X2 ),
% 2.48/1.03      inference(cnf_transformation,[],[f27]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_42,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1) != k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = X1
% 2.48/1.03      | k1_xboole_0 = X0
% 2.48/1.03      | k1_xboole_0 = sK1 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_57,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK1) != k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = X0
% 2.48/1.03      | k1_xboole_0 = sK1 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_42]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_330,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) != k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = sK1 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_57]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_386,plain,
% 2.48/1.03      ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) = sK1
% 2.48/1.03      | sK1 = k1_xboole_0 ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_113,c_31,c_33,c_330]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_401,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k1_xboole_0
% 2.48/1.03      | sK1 = sK0
% 2.48/1.03      | sK1 = k1_xboole_0
% 2.48/1.03      | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_386,c_0]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_59,plain,
% 2.48/1.03      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_71,plain,
% 2.48/1.03      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_59]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_72,plain,
% 2.48/1.03      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_71]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_105,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(X0,sK0),X1) != k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = X1
% 2.48/1.03      | k1_xboole_0 = X0
% 2.48/1.03      | k1_xboole_0 = sK0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_145,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(X0,sK0),sK0) != k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = X0
% 2.48/1.03      | k1_xboole_0 = sK0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_105]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_440,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) != k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = sK0 ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_145]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1183,plain,
% 2.48/1.03      ( sK1 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_401,c_6,c_58,c_72,c_84,c_440]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1185,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
% 2.48/1.03      | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_1183,c_7]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1190,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k1_xboole_0
% 2.48/1.03      | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(demodulation,[status(thm)],[c_1185,c_3]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1320,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k1_relat_1(k1_xboole_0)
% 2.48/1.03      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k1_xboole_0
% 2.48/1.03      | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_1190,c_1]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2691,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k1_relat_1(k1_xboole_0)
% 2.48/1.03      | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_1320,c_72,c_84,c_440]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2703,plain,
% 2.48/1.03      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_2691,c_5]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1323,plain,
% 2.48/1.03      ( k2_zfmisc_1(sK0,sK0) = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_1190,c_5]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2697,plain,
% 2.48/1.03      ( k2_zfmisc_1(k1_xboole_0,sK0) = k1_relat_1(k1_xboole_0)
% 2.48/1.03      | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_1323,c_2691]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_81,plain,
% 2.48/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_3,c_3]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2713,plain,
% 2.48/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(demodulation,[status(thm)],[c_2697,c_81]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2718,plain,
% 2.48/1.03      ( sK0 = k1_xboole_0 ),
% 2.48/1.03      inference(global_propositional_subsumption,[status(thm)],[c_2703,c_2713]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_178,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),X0) != k1_xboole_0
% 2.48/1.03      | k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) = k1_xboole_0
% 2.48/1.03      | sK1 = k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = X0 ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_560,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),X0) != k1_xboole_0
% 2.48/1.03      | sK1 = k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = X0 ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_178,c_31,c_33,c_330]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2728,plain,
% 2.48/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0),X0) != k1_xboole_0
% 2.48/1.03      | sK1 = k1_xboole_0
% 2.48/1.03      | k1_xboole_0 = X0 ),
% 2.48/1.03      inference(demodulation,[status(thm)],[c_2718,c_560]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2745,plain,
% 2.48/1.03      ( sK1 = k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 != k1_xboole_0 ),
% 2.48/1.03      inference(demodulation,[status(thm)],[c_2728,c_3]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2746,plain,
% 2.48/1.03      ( sK1 = k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.48/1.03      inference(equality_resolution_simp,[status(thm)],[c_2745]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2992,plain,
% 2.48/1.03      ( k1_xboole_0 = X0 ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_162,c_6,c_58,c_68,c_84,c_2703,c_2713,c_2746]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2736,plain,
% 2.48/1.03      ( sK1 != k1_xboole_0 ),
% 2.48/1.03      inference(demodulation,[status(thm)],[c_2718,c_6]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3002,plain,
% 2.48/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 2.48/1.03      inference(demodulation,[status(thm)],[c_2992,c_2736]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3003,plain,
% 2.48/1.03      ( $false ),
% 2.48/1.03      inference(equality_resolution_simp,[status(thm)],[c_3002]) ).
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.03  
% 2.48/1.03  ------                               Statistics
% 2.48/1.03  
% 2.48/1.03  ------ General
% 2.48/1.03  
% 2.48/1.03  abstr_ref_over_cycles:                  0
% 2.48/1.03  abstr_ref_under_cycles:                 0
% 2.48/1.03  gc_basic_clause_elim:                   0
% 2.48/1.03  forced_gc_time:                         0
% 2.48/1.03  parsing_time:                           0.042
% 2.48/1.03  unif_index_cands_time:                  0.
% 2.48/1.03  unif_index_add_time:                    0.
% 2.48/1.03  orderings_time:                         0.
% 2.48/1.03  out_proof_time:                         0.008
% 2.48/1.03  total_time:                             0.201
% 2.48/1.03  num_of_symbols:                         37
% 2.48/1.03  num_of_terms:                           2156
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing
% 2.48/1.03  
% 2.48/1.03  num_of_splits:                          0
% 2.48/1.03  num_of_split_atoms:                     0
% 2.48/1.03  num_of_reused_defs:                     0
% 2.48/1.03  num_eq_ax_congr_red:                    0
% 2.48/1.03  num_of_sem_filtered_clauses:            0
% 2.48/1.03  num_of_subtypes:                        0
% 2.48/1.03  monotx_restored_types:                  0
% 2.48/1.03  sat_num_of_epr_types:                   0
% 2.48/1.03  sat_num_of_non_cyclic_types:            0
% 2.48/1.03  sat_guarded_non_collapsed_types:        0
% 2.48/1.03  num_pure_diseq_elim:                    0
% 2.48/1.03  simp_replaced_by:                       0
% 2.48/1.03  res_preprocessed:                       21
% 2.48/1.03  prep_upred:                             0
% 2.48/1.03  prep_unflattend:                        0
% 2.48/1.03  smt_new_axioms:                         0
% 2.48/1.03  pred_elim_cands:                        0
% 2.48/1.03  pred_elim:                              0
% 2.48/1.03  pred_elim_cl:                           0
% 2.48/1.03  pred_elim_cycles:                       0
% 2.48/1.03  merged_defs:                            0
% 2.48/1.03  merged_defs_ncl:                        0
% 2.48/1.03  bin_hyper_res:                          0
% 2.48/1.03  prep_cycles:                            2
% 2.48/1.03  pred_elim_time:                         0.
% 2.48/1.03  splitting_time:                         0.
% 2.48/1.03  sem_filter_time:                        0.
% 2.48/1.03  monotx_time:                            0.
% 2.48/1.03  subtype_inf_time:                       0.
% 2.48/1.03  
% 2.48/1.03  ------ Problem properties
% 2.48/1.03  
% 2.48/1.03  clauses:                                8
% 2.48/1.03  conjectures:                            2
% 2.48/1.03  epr:                                    1
% 2.48/1.03  horn:                                   5
% 2.48/1.03  ground:                                 2
% 2.48/1.03  unary:                                  5
% 2.48/1.03  binary:                                 0
% 2.48/1.03  lits:                                   15
% 2.48/1.03  lits_eq:                                15
% 2.48/1.03  fd_pure:                                0
% 2.48/1.03  fd_pseudo:                              0
% 2.48/1.03  fd_cond:                                1
% 2.48/1.03  fd_pseudo_cond:                         0
% 2.48/1.03  ac_symbols:                             0
% 2.48/1.03  
% 2.48/1.03  ------ Propositional Solver
% 2.48/1.03  
% 2.48/1.03  prop_solver_calls:                      29
% 2.48/1.03  prop_fast_solver_calls:                 307
% 2.48/1.03  smt_solver_calls:                       0
% 2.48/1.03  smt_fast_solver_calls:                  0
% 2.48/1.03  prop_num_of_clauses:                    723
% 2.48/1.03  prop_preprocess_simplified:             1353
% 2.48/1.03  prop_fo_subsumed:                       25
% 2.48/1.03  prop_solver_time:                       0.
% 2.48/1.03  smt_solver_time:                        0.
% 2.48/1.03  smt_fast_solver_time:                   0.
% 2.48/1.03  prop_fast_solver_time:                  0.
% 2.48/1.03  prop_unsat_core_time:                   0.
% 2.48/1.03  
% 2.48/1.03  ------ QBF
% 2.48/1.03  
% 2.48/1.03  qbf_q_res:                              0
% 2.48/1.03  qbf_num_tautologies:                    0
% 2.48/1.03  qbf_prep_cycles:                        0
% 2.48/1.03  
% 2.48/1.03  ------ BMC1
% 2.48/1.03  
% 2.48/1.03  bmc1_current_bound:                     -1
% 2.48/1.03  bmc1_last_solved_bound:                 -1
% 2.48/1.03  bmc1_unsat_core_size:                   -1
% 2.48/1.03  bmc1_unsat_core_parents_size:           -1
% 2.48/1.03  bmc1_merge_next_fun:                    0
% 2.48/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.48/1.03  
% 2.48/1.03  ------ Instantiation
% 2.48/1.03  
% 2.48/1.03  inst_num_of_clauses:                    280
% 2.48/1.03  inst_num_in_passive:                    145
% 2.48/1.03  inst_num_in_active:                     111
% 2.48/1.03  inst_num_in_unprocessed:                24
% 2.48/1.03  inst_num_of_loops:                      270
% 2.48/1.03  inst_num_of_learning_restarts:          0
% 2.48/1.03  inst_num_moves_active_passive:          144
% 2.48/1.03  inst_lit_activity:                      0
% 2.48/1.03  inst_lit_activity_moves:                0
% 2.48/1.03  inst_num_tautologies:                   0
% 2.48/1.03  inst_num_prop_implied:                  0
% 2.48/1.03  inst_num_existing_simplified:           0
% 2.48/1.03  inst_num_eq_res_simplified:             0
% 2.48/1.03  inst_num_child_elim:                    0
% 2.48/1.03  inst_num_of_dismatching_blockings:      54
% 2.48/1.03  inst_num_of_non_proper_insts:           286
% 2.48/1.03  inst_num_of_duplicates:                 0
% 2.48/1.03  inst_inst_num_from_inst_to_res:         0
% 2.48/1.03  inst_dismatching_checking_time:         0.
% 2.48/1.03  
% 2.48/1.03  ------ Resolution
% 2.48/1.03  
% 2.48/1.03  res_num_of_clauses:                     0
% 2.48/1.03  res_num_in_passive:                     0
% 2.48/1.03  res_num_in_active:                      0
% 2.48/1.03  res_num_of_loops:                       23
% 2.48/1.03  res_forward_subset_subsumed:            69
% 2.48/1.03  res_backward_subset_subsumed:           0
% 2.48/1.03  res_forward_subsumed:                   0
% 2.48/1.03  res_backward_subsumed:                  0
% 2.48/1.03  res_forward_subsumption_resolution:     0
% 2.48/1.03  res_backward_subsumption_resolution:    0
% 2.48/1.03  res_clause_to_clause_subsumption:       2578
% 2.48/1.03  res_orphan_elimination:                 0
% 2.48/1.03  res_tautology_del:                      49
% 2.48/1.03  res_num_eq_res_simplified:              0
% 2.48/1.03  res_num_sel_changes:                    0
% 2.48/1.03  res_moves_from_active_to_pass:          0
% 2.48/1.03  
% 2.48/1.03  ------ Superposition
% 2.48/1.03  
% 2.48/1.03  sup_time_total:                         0.
% 2.48/1.03  sup_time_generating:                    0.
% 2.48/1.03  sup_time_sim_full:                      0.
% 2.48/1.03  sup_time_sim_immed:                     0.
% 2.48/1.03  
% 2.48/1.03  sup_num_of_clauses:                     274
% 2.48/1.03  sup_num_in_active:                      2
% 2.48/1.03  sup_num_in_passive:                     272
% 2.48/1.03  sup_num_of_loops:                       52
% 2.48/1.03  sup_fw_superposition:                   498
% 2.48/1.03  sup_bw_superposition:                   1021
% 2.48/1.03  sup_immediate_simplified:               538
% 2.48/1.03  sup_given_eliminated:                   9
% 2.48/1.03  comparisons_done:                       0
% 2.48/1.03  comparisons_avoided:                    100
% 2.48/1.03  
% 2.48/1.03  ------ Simplifications
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  sim_fw_subset_subsumed:                 174
% 2.48/1.03  sim_bw_subset_subsumed:                 19
% 2.48/1.03  sim_fw_subsumed:                        200
% 2.48/1.03  sim_bw_subsumed:                        26
% 2.48/1.03  sim_fw_subsumption_res:                 0
% 2.48/1.03  sim_bw_subsumption_res:                 0
% 2.48/1.03  sim_tautology_del:                      47
% 2.48/1.03  sim_eq_tautology_del:                   314
% 2.48/1.03  sim_eq_res_simp:                        65
% 2.48/1.03  sim_fw_demodulated:                     189
% 2.48/1.03  sim_bw_demodulated:                     32
% 2.48/1.03  sim_light_normalised:                   6
% 2.48/1.03  sim_joinable_taut:                      0
% 2.48/1.03  sim_joinable_simp:                      0
% 2.48/1.03  sim_ac_normalised:                      0
% 2.48/1.03  sim_smt_subsumption:                    0
% 2.48/1.03  
%------------------------------------------------------------------------------
