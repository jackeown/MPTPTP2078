%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0895+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:21 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 392 expanded)
%              Number of clauses        :   30 (  92 expanded)
%              Number of leaves         :    5 (  76 expanded)
%              Depth                    :   26
%              Number of atoms          :  225 (2053 expanded)
%              Number of equality atoms :  224 (2052 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
          | ( k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
        | ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
      | ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f13])).

fof(f27,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f28,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f27,f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f26,f15])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f18])).

fof(f25,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f25,f15])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f17])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] : k3_zfmisc_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f22])).

fof(f24,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f24,f15])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X2,X0] : k3_zfmisc_1(X0,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f21])).

fof(f23,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f23,f15])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X2,X1] : k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f20])).

cnf(c_7,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_190,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_2])).

cnf(c_6,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_281,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_190,c_6])).

cnf(c_8,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_317,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) != k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_281,c_8])).

cnf(c_323,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_317,c_281])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_324,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_323,c_0])).

cnf(c_325,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_324])).

cnf(c_9,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_346,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,k1_xboole_0),sK3) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_325,c_9])).

cnf(c_361,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,k1_xboole_0),sK3) != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_346,c_325])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( k3_zfmisc_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_362,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_361,c_1,c_3])).

cnf(c_363,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_362])).

cnf(c_10,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_374,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,k1_xboole_0,sK2),sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_363,c_10])).

cnf(c_394,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,k1_xboole_0,sK2),sK3) != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_374,c_363])).

cnf(c_4,plain,
    ( k3_zfmisc_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_395,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_394,c_1,c_4])).

cnf(c_396,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_395])).

cnf(c_11,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_411,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(k1_xboole_0,sK1,sK2),sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_396,c_11])).

cnf(c_430,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(k1_xboole_0,sK1,sK2),sK3) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_411])).

cnf(c_5,plain,
    ( k3_zfmisc_1(k1_xboole_0,X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_432,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_430,c_1,c_5])).

cnf(c_433,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_432])).


%------------------------------------------------------------------------------
