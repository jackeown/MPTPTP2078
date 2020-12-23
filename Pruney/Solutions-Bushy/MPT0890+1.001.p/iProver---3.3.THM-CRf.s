%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0890+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:21 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   66 (1054 expanded)
%              Number of clauses        :   29 ( 272 expanded)
%              Number of leaves         :   10 ( 317 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 (5649 expanded)
%              Number of equality atoms :  215 (4830 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                  & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                  & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k2_mcart_1(X3) != k7_mcart_1(X0,X1,X2,X3)
            | k2_mcart_1(k1_mcart_1(X3)) != k6_mcart_1(X0,X1,X2,X3)
            | k1_mcart_1(k1_mcart_1(X3)) != k5_mcart_1(X0,X1,X2,X3) )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k2_mcart_1(X3) != k7_mcart_1(X0,X1,X2,X3)
            | k2_mcart_1(k1_mcart_1(X3)) != k6_mcart_1(X0,X1,X2,X3)
            | k1_mcart_1(k1_mcart_1(X3)) != k5_mcart_1(X0,X1,X2,X3) )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k2_mcart_1(sK7) != k7_mcart_1(X0,X1,X2,sK7)
          | k2_mcart_1(k1_mcart_1(sK7)) != k6_mcart_1(X0,X1,X2,sK7)
          | k1_mcart_1(k1_mcart_1(sK7)) != k5_mcart_1(X0,X1,X2,sK7) )
        & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k2_mcart_1(X3) != k7_mcart_1(X0,X1,X2,X3)
              | k2_mcart_1(k1_mcart_1(X3)) != k6_mcart_1(X0,X1,X2,X3)
              | k1_mcart_1(k1_mcart_1(X3)) != k5_mcart_1(X0,X1,X2,X3) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k2_mcart_1(X3) != k7_mcart_1(sK4,sK5,sK6,X3)
            | k2_mcart_1(k1_mcart_1(X3)) != k6_mcart_1(sK4,sK5,sK6,X3)
            | k1_mcart_1(k1_mcart_1(X3)) != k5_mcart_1(sK4,sK5,sK6,X3) )
          & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6)) )
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( k2_mcart_1(sK7) != k7_mcart_1(sK4,sK5,sK6,sK7)
      | k2_mcart_1(k1_mcart_1(sK7)) != k6_mcart_1(sK4,sK5,sK6,sK7)
      | k1_mcart_1(k1_mcart_1(sK7)) != k5_mcart_1(sK4,sK5,sK6,sK7) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f12,f22,f21])).

fof(f35,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK3(X0,X1) != X1
        & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK3(X0,X1) != X1
              & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).

fof(f27,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f27])).

fof(f45,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_mcart_1(k4_tarski(X4,X5)) = X5
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK0(X0,X1) != X1
        & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK0(X0,X1) != X1
              & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f24,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f24])).

fof(f41,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_mcart_1(k4_tarski(X4,X5)) = X4
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f40])).

fof(f36,plain,
    ( k2_mcart_1(sK7) != k7_mcart_1(sK4,sK5,sK6,sK7)
    | k2_mcart_1(k1_mcart_1(sK7)) != k6_mcart_1(sK4,sK5,sK6,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) != k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_51,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK4,sK5,sK6)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | sK7 != X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_52,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK4,sK5,sK6)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK7),k6_mcart_1(X0,X1,X2,sK7)),k7_mcart_1(X0,X1,X2,sK7)) = sK7
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_51])).

cnf(c_195,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_52])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_87,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_158,plain,
    ( k3_zfmisc_1(sK4,sK5,sK6) = k3_zfmisc_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_159,plain,
    ( k3_zfmisc_1(sK4,sK5,sK6) != k3_zfmisc_1(sK4,sK5,sK6)
    | k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_196,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_195,c_11,c_10,c_9,c_158,c_159])).

cnf(c_5,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_471,plain,
    ( k4_tarski(X0,X1) != sK7
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7))) = k7_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_196,c_5])).

cnf(c_626,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7)
    | k4_tarski(X0,X1) != sK7 ),
    inference(light_normalisation,[status(thm)],[c_471,c_196])).

cnf(c_686,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7) ),
    inference(superposition,[status(thm)],[c_196,c_626])).

cnf(c_690,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k2_mcart_1(sK7)) = sK7 ),
    inference(demodulation,[status(thm)],[c_686,c_196])).

cnf(c_2,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_344,plain,
    ( k4_tarski(X0,X1) != sK7
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7))) = k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_196,c_2])).

cnf(c_457,plain,
    ( k4_tarski(X0,X1) != sK7
    | k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)) = k1_mcart_1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_344,c_196])).

cnf(c_834,plain,
    ( k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)) = k1_mcart_1(sK7) ),
    inference(superposition,[status(thm)],[c_690,c_457])).

cnf(c_474,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[status(thm)],[c_5])).

cnf(c_2431,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(superposition,[status(thm)],[c_834,c_474])).

cnf(c_347,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[status(thm)],[c_2])).

cnf(c_2432,plain,
    ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(superposition,[status(thm)],[c_834,c_347])).

cnf(c_7,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(sK7)) != k6_mcart_1(sK4,sK5,sK6,sK7)
    | k2_mcart_1(sK7) != k7_mcart_1(sK4,sK5,sK6,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) != k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_691,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) != k2_mcart_1(k1_mcart_1(sK7))
    | k5_mcart_1(sK4,sK5,sK6,sK7) != k1_mcart_1(k1_mcart_1(sK7))
    | k2_mcart_1(sK7) != k2_mcart_1(sK7) ),
    inference(demodulation,[status(thm)],[c_686,c_7])).

cnf(c_692,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) != k2_mcart_1(k1_mcart_1(sK7))
    | k5_mcart_1(sK4,sK5,sK6,sK7) != k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(equality_resolution_simp,[status(thm)],[c_691])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2431,c_2432,c_692])).


%------------------------------------------------------------------------------
