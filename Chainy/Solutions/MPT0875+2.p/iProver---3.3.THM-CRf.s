%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0875+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 31.23s
% Output     : CNFRefutation 31.23s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 319 expanded)
%              Number of clauses        :   21 (  45 expanded)
%              Number of leaves         :    5 (  95 expanded)
%              Depth                    :   22
%              Number of atoms          :  154 ( 982 expanded)
%              Number of equality atoms :  153 ( 981 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1321,conjecture,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1322,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    inference(negated_conjecture,[],[f1321])).

fof(f2672,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    inference(ennf_transformation,[],[f1322])).

fof(f3685,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f2672])).

fof(f3686,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f3685])).

fof(f3687,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
          | ( k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k3_zfmisc_1(sK379,sK380,sK381)
        | k1_xboole_0 = sK381
        | k1_xboole_0 = sK380
        | k1_xboole_0 = sK379 )
      & ( k1_xboole_0 != k3_zfmisc_1(sK379,sK380,sK381)
        | ( k1_xboole_0 != sK381
          & k1_xboole_0 != sK380
          & k1_xboole_0 != sK379 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3688,plain,
    ( ( k1_xboole_0 = k3_zfmisc_1(sK379,sK380,sK381)
      | k1_xboole_0 = sK381
      | k1_xboole_0 = sK380
      | k1_xboole_0 = sK379 )
    & ( k1_xboole_0 != k3_zfmisc_1(sK379,sK380,sK381)
      | ( k1_xboole_0 != sK381
        & k1_xboole_0 != sK380
        & k1_xboole_0 != sK379 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK379,sK380,sK381])],[f3686,f3687])).

fof(f6012,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK379,sK380,sK381)
    | k1_xboole_0 = sK381
    | k1_xboole_0 = sK380
    | k1_xboole_0 = sK379 ),
    inference(cnf_transformation,[],[f3688])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5896,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3706,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6756,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | o_0_0_xboole_0 = sK381
    | o_0_0_xboole_0 = sK380
    | o_0_0_xboole_0 = sK379 ),
    inference(definition_unfolding,[],[f6012,f3706,f5896,f3706,f3706,f3706])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2868,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f2869,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2868])).

fof(f4161,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2869])).

fof(f6315,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f4161,f3706,f3706,f3706])).

fof(f6011,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK379,sK380,sK381)
    | k1_xboole_0 != sK381 ),
    inference(cnf_transformation,[],[f3688])).

fof(f6757,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | o_0_0_xboole_0 != sK381 ),
    inference(definition_unfolding,[],[f6011,f3706,f5896,f3706])).

fof(f4163,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2869])).

fof(f6313,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f4163,f3706,f3706])).

fof(f6839,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f6313])).

fof(f6010,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK379,sK380,sK381)
    | k1_xboole_0 != sK380 ),
    inference(cnf_transformation,[],[f3688])).

fof(f6758,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | o_0_0_xboole_0 != sK380 ),
    inference(definition_unfolding,[],[f6010,f3706,f5896,f3706])).

fof(f4162,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2869])).

fof(f6314,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f4162,f3706,f3706])).

fof(f6840,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f6314])).

fof(f6009,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK379,sK380,sK381)
    | k1_xboole_0 != sK379 ),
    inference(cnf_transformation,[],[f3688])).

fof(f6759,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | o_0_0_xboole_0 != sK379 ),
    inference(definition_unfolding,[],[f6009,f3706,f5896,f3706])).

cnf(c_2292,negated_conjecture,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | o_0_0_xboole_0 = sK381
    | o_0_0_xboole_0 = sK380
    | o_0_0_xboole_0 = sK379 ),
    inference(cnf_transformation,[],[f6756])).

cnf(c_452,plain,
    ( k2_zfmisc_1(X0,X1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f6315])).

cnf(c_89437,plain,
    ( k2_zfmisc_1(sK379,sK380) = o_0_0_xboole_0
    | sK381 = o_0_0_xboole_0
    | sK380 = o_0_0_xboole_0
    | sK379 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2292,c_452])).

cnf(c_89566,plain,
    ( sK381 = o_0_0_xboole_0
    | sK380 = o_0_0_xboole_0
    | sK379 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_89437,c_452])).

cnf(c_2293,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | o_0_0_xboole_0 != sK381 ),
    inference(cnf_transformation,[],[f6757])).

cnf(c_91630,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),o_0_0_xboole_0) != o_0_0_xboole_0
    | sK381 != o_0_0_xboole_0
    | sK380 = o_0_0_xboole_0
    | sK379 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_89566,c_2293])).

cnf(c_91635,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),o_0_0_xboole_0) != o_0_0_xboole_0
    | sK380 = o_0_0_xboole_0
    | sK379 = o_0_0_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_91630,c_89566])).

cnf(c_450,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6839])).

cnf(c_91636,plain,
    ( sK380 = o_0_0_xboole_0
    | sK379 = o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_91635,c_450])).

cnf(c_91637,plain,
    ( sK380 = o_0_0_xboole_0
    | sK379 = o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_91636])).

cnf(c_2294,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | o_0_0_xboole_0 != sK380 ),
    inference(cnf_transformation,[],[f6758])).

cnf(c_92079,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,o_0_0_xboole_0),sK381) != o_0_0_xboole_0
    | sK380 != o_0_0_xboole_0
    | sK379 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_91637,c_2294])).

cnf(c_92091,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,o_0_0_xboole_0),sK381) != o_0_0_xboole_0
    | sK379 = o_0_0_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_92079,c_91637])).

cnf(c_451,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6840])).

cnf(c_92092,plain,
    ( sK379 = o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_92091,c_450,c_451])).

cnf(c_92093,plain,
    ( sK379 = o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_92092])).

cnf(c_2295,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | o_0_0_xboole_0 != sK379 ),
    inference(cnf_transformation,[],[f6759])).

cnf(c_92145,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK380),sK381) != o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_92093,c_2295])).

cnf(c_92158,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK380),sK381) != o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_92145])).

cnf(c_92160,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_92158,c_451])).

cnf(c_92161,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_92160])).

%------------------------------------------------------------------------------
