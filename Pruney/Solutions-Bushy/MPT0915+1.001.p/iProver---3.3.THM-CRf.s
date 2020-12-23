%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:24 EST 2020

% Result     : Theorem 1.35s
% Output     : CNFRefutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 384 expanded)
%              Number of clauses        :   52 ( 134 expanded)
%              Number of leaves         :    7 ( 146 expanded)
%              Depth                    :   15
%              Number of atoms          :  264 (3188 expanded)
%              Number of equality atoms :  233 (2629 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( ? [X6] :
            ( ? [X7] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                    & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                    & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ~ ( ? [X6] :
              ( ? [X7] :
                  ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                      & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                      & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                  & X6 = X7
                  & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & k1_xboole_0 != X5
          & k1_xboole_0 != X4
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
                | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
                | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
              & X6 = X7
              & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X5
      & k1_xboole_0 != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
            | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
            | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
          & X6 = X7
          & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
     => ( ( k7_mcart_1(X3,X4,X5,sK7) != k7_mcart_1(X0,X1,X2,X6)
          | k6_mcart_1(X3,X4,X5,sK7) != k6_mcart_1(X0,X1,X2,X6)
          | k5_mcart_1(X3,X4,X5,sK7) != k5_mcart_1(X0,X1,X2,X6) )
        & sK7 = X6
        & m1_subset_1(sK7,k3_zfmisc_1(X3,X4,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
                | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
                | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
              & X6 = X7
              & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
     => ( ? [X7] :
            ( ( k7_mcart_1(X0,X1,X2,sK6) != k7_mcart_1(X3,X4,X5,X7)
              | k6_mcart_1(X0,X1,X2,sK6) != k6_mcart_1(X3,X4,X5,X7)
              | k5_mcart_1(X0,X1,X2,sK6) != k5_mcart_1(X3,X4,X5,X7) )
            & sK6 = X7
            & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
        & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
                  | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
                  | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( k7_mcart_1(sK0,sK1,sK2,X6) != k7_mcart_1(sK3,sK4,sK5,X7)
                | k6_mcart_1(sK0,sK1,sK2,X6) != k6_mcart_1(sK3,sK4,sK5,X7)
                | k5_mcart_1(sK0,sK1,sK2,X6) != k5_mcart_1(sK3,sK4,sK5,X7) )
              & X6 = X7
              & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
      | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
      | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) )
    & sK6 = sK7
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f5,f8,f7,f6])).

fof(f19,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f22,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
    | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
    | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_309,plain,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_311,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1269,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_309,c_311])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_208,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_225,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_209,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_391,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_392,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_393,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_394,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_395,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_396,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_1529,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1269,c_12,c_11,c_10,c_225,c_392,c_394,c_396])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_313,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1422,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_309,c_313])).

cnf(c_1470,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_12,c_11,c_10,c_225,c_392,c_394,c_396])).

cnf(c_3,negated_conjecture,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7)
    | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
    | k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_363,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) != k5_mcart_1(sK0,sK1,sK2,sK6)
    | k6_mcart_1(sK3,sK4,sK5,sK6) != k6_mcart_1(sK0,sK1,sK2,sK6)
    | k7_mcart_1(sK3,sK4,sK5,sK6) != k7_mcart_1(sK0,sK1,sK2,sK6) ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_1473,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) != k5_mcart_1(sK0,sK1,sK2,sK6)
    | k6_mcart_1(sK3,sK4,sK5,sK6) != k6_mcart_1(sK0,sK1,sK2,sK6)
    | k7_mcart_1(sK3,sK4,sK5,sK6) != k2_mcart_1(sK6) ),
    inference(demodulation,[status(thm)],[c_1470,c_363])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_385,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_386,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_387,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_388,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_389,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_390,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_5,negated_conjecture,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_310,plain,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_330,plain,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_310,c_4])).

cnf(c_1423,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_330,c_313])).

cnf(c_1498,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) != k6_mcart_1(sK0,sK1,sK2,sK6)
    | k5_mcart_1(sK3,sK4,sK5,sK6) != k5_mcart_1(sK0,sK1,sK2,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1473,c_9,c_8,c_7,c_225,c_386,c_388,c_390,c_1423])).

cnf(c_1499,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) != k5_mcart_1(sK0,sK1,sK2,sK6)
    | k6_mcart_1(sK3,sK4,sK5,sK6) != k6_mcart_1(sK0,sK1,sK2,sK6) ),
    inference(renaming,[status(thm)],[c_1498])).

cnf(c_1532,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | k6_mcart_1(sK3,sK4,sK5,sK6) != k6_mcart_1(sK0,sK1,sK2,sK6) ),
    inference(demodulation,[status(thm)],[c_1529,c_1499])).

cnf(c_1272,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_330,c_311])).

cnf(c_1590,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) != k6_mcart_1(sK0,sK1,sK2,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1532,c_9,c_8,c_7,c_225,c_386,c_388,c_390,c_1272])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_312,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1446,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_309,c_312])).

cnf(c_1536,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1446,c_12,c_11,c_10,c_225,c_392,c_394,c_396])).

cnf(c_1447,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_330,c_312])).

cnf(c_1539,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1447,c_9,c_8,c_7,c_225,c_386,c_388,c_390])).

cnf(c_1592,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) != k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(light_normalisation,[status(thm)],[c_1590,c_1536,c_1539])).

cnf(c_1593,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1592])).


%------------------------------------------------------------------------------
