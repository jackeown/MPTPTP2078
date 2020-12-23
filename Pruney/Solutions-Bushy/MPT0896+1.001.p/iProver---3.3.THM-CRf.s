%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0896+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:21 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 386 expanded)
%              Number of clauses        :   42 ( 109 expanded)
%              Number of leaves         :    7 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 (2336 expanded)
%              Number of equality atoms :  290 (2335 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f15])).

fof(f27,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    inference(definition_unfolding,[],[f27,f17,f17])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f7])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X2,X1] : k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f9])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_14,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( X0 = X1
    | k2_zfmisc_1(X0,X2) != k2_zfmisc_1(X1,X3)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_345,plain,
    ( k3_zfmisc_1(sK4,sK5,sK6) = X0
    | k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_14,c_1])).

cnf(c_437,plain,
    ( k3_zfmisc_1(sK4,sK5,sK6) = k3_zfmisc_1(sK0,sK1,sK2)
    | k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_345])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_16,plain,
    ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k3_zfmisc_1(k1_xboole_0,X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,plain,
    ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_24,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_116,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_117,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_112,plain,
    ( k3_zfmisc_1(X0,sK1,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_159,plain,
    ( k3_zfmisc_1(sK0,sK1,X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_256,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_588,plain,
    ( k3_zfmisc_1(sK4,sK5,sK6) = k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_13,c_12,c_11,c_10,c_16,c_17,c_117,c_256])).

cnf(c_8,plain,
    ( X0 = X1
    | k3_zfmisc_1(X1,X2,X3) != k3_zfmisc_1(X0,X4,X5)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X5 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_602,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK4 = X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_588,c_8])).

cnf(c_920,plain,
    ( sK4 = sK0
    | sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_602])).

cnf(c_6,plain,
    ( X0 = X1
    | k3_zfmisc_1(X2,X3,X0) != k3_zfmisc_1(X4,X5,X1)
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_599,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK6 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_588,c_6])).

cnf(c_807,plain,
    ( sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK6 = sK2
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_599])).

cnf(c_7,plain,
    ( X0 = X1
    | k3_zfmisc_1(X2,X0,X3) != k3_zfmisc_1(X4,X1,X5)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X4
    | k1_xboole_0 = X5 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_597,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK5 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_588,c_7])).

cnf(c_789,plain,
    ( sK0 = k1_xboole_0
    | sK5 = sK1
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_597])).

cnf(c_0,plain,
    ( X0 = X1
    | k2_zfmisc_1(X2,X0) != k2_zfmisc_1(X3,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_289,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k2_zfmisc_1(X0,X1)
    | sK7 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_14,c_0])).

cnf(c_400,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_289])).

cnf(c_469,plain,
    ( sK7 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_13,c_12,c_11,c_10,c_16,c_17,c_117,c_256])).

cnf(c_9,negated_conjecture,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_475,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_469,c_9])).

cnf(c_479,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_475])).

cnf(c_122,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_123,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_120,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_121,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_118,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_119,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_920,c_807,c_789,c_479,c_123,c_121,c_119,c_17,c_16,c_11,c_12,c_13])).


%------------------------------------------------------------------------------
