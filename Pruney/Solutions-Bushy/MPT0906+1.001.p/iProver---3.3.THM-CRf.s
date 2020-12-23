%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0906+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:23 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  72 expanded)
%              Number of clauses        :   19 (  21 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 267 expanded)
%              Number of equality atoms :  101 ( 214 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
     => ( ( k2_mcart_1(sK2) = sK2
          | k1_mcart_1(sK2) = sK2 )
        & m1_subset_1(sK2,k2_zfmisc_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k2_zfmisc_1(X0,X1) != k1_xboole_0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10,f9])).

fof(f18,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,plain,(
    k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f13])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k2_mcart_1(X0) != X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_60,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k2_mcart_1(X2) != X2
    | sK2 != X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_61,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k2_mcart_1(sK2) != sK2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_60])).

cnf(c_5,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k1_mcart_1(X0) != X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_45,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k1_mcart_1(X2) != X2
    | sK2 != X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_46,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k1_mcart_1(sK2) != sK2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_45])).

cnf(c_63,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_61,c_5,c_46])).

cnf(c_147,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_63])).

cnf(c_7,negated_conjecture,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_151,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_147,c_7])).

cnf(c_242,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_151])).

cnf(c_243,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_242])).

cnf(c_249,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_243,c_7])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_344,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_249,c_1])).

cnf(c_345,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_344])).


%------------------------------------------------------------------------------
