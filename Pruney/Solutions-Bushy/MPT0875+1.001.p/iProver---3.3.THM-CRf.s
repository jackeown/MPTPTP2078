%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0875+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:18 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 246 expanded)
%              Number of clauses        :   33 ( 101 expanded)
%              Number of leaves         :    6 (  53 expanded)
%              Depth                    :   22
%              Number of atoms          :  175 ( 968 expanded)
%              Number of equality atoms :  174 ( 967 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
          | ( k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0
        | ( k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0
      | ( k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f19,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f19,f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f18,f12])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f15])).

fof(f17,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f17,f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f14])).

fof(f16,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f16,f12])).

cnf(c_3,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_177,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_48,plain,
    ( k2_zfmisc_1(X0,sK1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_65,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_13,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_87,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_97,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_99,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_12,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_98,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_89,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_166,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_168,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_167,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_186,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_177,c_65,c_99,c_98,c_168,c_167])).

cnf(c_4,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_194,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_186,c_4])).

cnf(c_199,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_194,c_186])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_200,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_199,c_0])).

cnf(c_201,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_200])).

cnf(c_5,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_239,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_201,c_5])).

cnf(c_251,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2) != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_239,c_201])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_252,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_251,c_0,c_1])).

cnf(c_253,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_252])).

cnf(c_6,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_259,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_253,c_6])).

cnf(c_272,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_259])).

cnf(c_274,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_272,c_1])).

cnf(c_275,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_274])).


%------------------------------------------------------------------------------
