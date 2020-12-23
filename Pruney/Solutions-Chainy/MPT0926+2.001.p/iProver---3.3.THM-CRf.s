%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:30 EST 2020

% Result     : Theorem 0.94s
% Output     : CNFRefutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 602 expanded)
%              Number of clauses        :   66 ( 210 expanded)
%              Number of leaves         :    7 ( 232 expanded)
%              Depth                    :   18
%              Number of atoms          :  363 (6109 expanded)
%              Number of equality atoms :  330 (5232 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ~ ( ? [X8] :
            ( ? [X9] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                    & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                    & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                    & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                & X8 = X9
                & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X7
        & k1_xboole_0 != X6
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ~ ( ? [X8] :
              ( ? [X9] :
                  ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                      & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                      & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                      & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                  & X8 = X9
                  & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
              & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
          & k1_xboole_0 != X7
          & k1_xboole_0 != X6
          & k1_xboole_0 != X5
          & k1_xboole_0 != X4
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ? [X8] :
          ( ? [X9] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9)
                | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9)
                | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9)
                | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9) )
              & X8 = X9
              & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X7
      & k1_xboole_0 != X6
      & k1_xboole_0 != X5
      & k1_xboole_0 != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ? [X9] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9)
            | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9)
            | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9)
            | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9) )
          & X8 = X9
          & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
     => ( ( k11_mcart_1(X4,X5,X6,X7,sK9) != k11_mcart_1(X0,X1,X2,X3,X8)
          | k10_mcart_1(X4,X5,X6,X7,sK9) != k10_mcart_1(X0,X1,X2,X3,X8)
          | k9_mcart_1(X4,X5,X6,X7,sK9) != k9_mcart_1(X0,X1,X2,X3,X8)
          | k8_mcart_1(X4,X5,X6,X7,sK9) != k8_mcart_1(X0,X1,X2,X3,X8) )
        & sK9 = X8
        & m1_subset_1(sK9,k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ? [X8] :
          ( ? [X9] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9)
                | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9)
                | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9)
                | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9) )
              & X8 = X9
              & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( ? [X9] :
            ( ( k11_mcart_1(X0,X1,X2,X3,sK8) != k11_mcart_1(X4,X5,X6,X7,X9)
              | k10_mcart_1(X0,X1,X2,X3,sK8) != k10_mcart_1(X4,X5,X6,X7,X9)
              | k9_mcart_1(X0,X1,X2,X3,sK8) != k9_mcart_1(X4,X5,X6,X7,X9)
              | k8_mcart_1(X0,X1,X2,X3,sK8) != k8_mcart_1(X4,X5,X6,X7,X9) )
            & sK8 = X9
            & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
        & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ? [X8] :
            ( ? [X9] :
                ( ( k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9)
                  | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9)
                  | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9)
                  | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9) )
                & X8 = X9
                & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X7
        & k1_xboole_0 != X6
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X8] :
          ( ? [X9] :
              ( ( k11_mcart_1(sK0,sK1,sK2,sK3,X8) != k11_mcart_1(sK4,sK5,sK6,sK7,X9)
                | k10_mcart_1(sK0,sK1,sK2,sK3,X8) != k10_mcart_1(sK4,sK5,sK6,sK7,X9)
                | k9_mcart_1(sK0,sK1,sK2,sK3,X8) != k9_mcart_1(sK4,sK5,sK6,sK7,X9)
                | k8_mcart_1(sK0,sK1,sK2,sK3,X8) != k8_mcart_1(sK4,sK5,sK6,sK7,X9) )
              & X8 = X9
              & m1_subset_1(X9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
          & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9) )
    & sK8 = sK9
    & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f5,f8,f7,f6])).

fof(f22,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
                & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
            & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f25,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_417,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_419,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3404,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_417,c_419])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_300,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_319,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_301,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_528,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_529,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_530,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_531,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_532,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_533,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_534,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_535,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_3455,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3404,c_15,c_14,c_13,c_12,c_319,c_529,c_531,c_533,c_535])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_421,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2244,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_417,c_421])).

cnf(c_3326,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2244,c_15,c_14,c_13,c_12,c_319,c_529,c_531,c_533,c_535])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_422,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1755,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_417,c_422])).

cnf(c_2684,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1755,c_15,c_14,c_13,c_12,c_319,c_529,c_531,c_533,c_535])).

cnf(c_4,negated_conjecture,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,negated_conjecture,
    ( sK8 = sK9 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_494,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k11_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
    inference(light_normalisation,[status(thm)],[c_4,c_5])).

cnf(c_2687,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8) ),
    inference(demodulation,[status(thm)],[c_2684,c_494])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_520,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_521,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_522,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_523,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_524,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_525,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_526,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_527,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_418,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_443,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_418,c_5])).

cnf(c_1756,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_443,c_422])).

cnf(c_2688,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2687,c_11,c_10,c_9,c_8,c_319,c_521,c_523,c_525,c_527,c_1756])).

cnf(c_2689,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
    inference(renaming,[status(thm)],[c_2688])).

cnf(c_3329,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(demodulation,[status(thm)],[c_3326,c_2689])).

cnf(c_2245,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_443,c_421])).

cnf(c_3333,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3329,c_11,c_10,c_9,c_8,c_319,c_521,c_523,c_525,c_527,c_2245])).

cnf(c_3334,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
    inference(renaming,[status(thm)],[c_3333])).

cnf(c_3458,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
    inference(demodulation,[status(thm)],[c_3455,c_3334])).

cnf(c_3405,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_443,c_419])).

cnf(c_3528,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3458,c_11,c_10,c_9,c_8,c_319,c_521,c_523,c_525,c_527,c_3405])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_420,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3433,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_417,c_420])).

cnf(c_3462,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3433,c_15,c_14,c_13,c_12,c_319,c_529,c_531,c_533,c_535])).

cnf(c_3434,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_443,c_420])).

cnf(c_3465,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3434,c_11,c_10,c_9,c_8,c_319,c_521,c_523,c_525,c_527])).

cnf(c_3530,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(light_normalisation,[status(thm)],[c_3528,c_3462,c_3465])).

cnf(c_3531,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3530])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.94/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.94/1.04  
% 0.94/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.94/1.04  
% 0.94/1.04  ------  iProver source info
% 0.94/1.04  
% 0.94/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.94/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.94/1.04  git: non_committed_changes: false
% 0.94/1.04  git: last_make_outside_of_git: false
% 0.94/1.04  
% 0.94/1.04  ------ 
% 0.94/1.04  
% 0.94/1.04  ------ Input Options
% 0.94/1.04  
% 0.94/1.04  --out_options                           all
% 0.94/1.04  --tptp_safe_out                         true
% 0.94/1.04  --problem_path                          ""
% 0.94/1.04  --include_path                          ""
% 0.94/1.04  --clausifier                            res/vclausify_rel
% 0.94/1.04  --clausifier_options                    --mode clausify
% 0.94/1.04  --stdin                                 false
% 0.94/1.04  --stats_out                             all
% 0.94/1.04  
% 0.94/1.04  ------ General Options
% 0.94/1.04  
% 0.94/1.04  --fof                                   false
% 0.94/1.04  --time_out_real                         305.
% 0.94/1.04  --time_out_virtual                      -1.
% 0.94/1.04  --symbol_type_check                     false
% 0.94/1.04  --clausify_out                          false
% 0.94/1.04  --sig_cnt_out                           false
% 0.94/1.04  --trig_cnt_out                          false
% 0.94/1.04  --trig_cnt_out_tolerance                1.
% 0.94/1.04  --trig_cnt_out_sk_spl                   false
% 0.94/1.04  --abstr_cl_out                          false
% 0.94/1.04  
% 0.94/1.04  ------ Global Options
% 0.94/1.04  
% 0.94/1.04  --schedule                              default
% 0.94/1.04  --add_important_lit                     false
% 0.94/1.04  --prop_solver_per_cl                    1000
% 0.94/1.04  --min_unsat_core                        false
% 0.94/1.04  --soft_assumptions                      false
% 0.94/1.04  --soft_lemma_size                       3
% 0.94/1.04  --prop_impl_unit_size                   0
% 0.94/1.04  --prop_impl_unit                        []
% 0.94/1.04  --share_sel_clauses                     true
% 0.94/1.04  --reset_solvers                         false
% 0.94/1.04  --bc_imp_inh                            [conj_cone]
% 0.94/1.04  --conj_cone_tolerance                   3.
% 0.94/1.04  --extra_neg_conj                        none
% 0.94/1.04  --large_theory_mode                     true
% 0.94/1.04  --prolific_symb_bound                   200
% 0.94/1.04  --lt_threshold                          2000
% 0.94/1.04  --clause_weak_htbl                      true
% 0.94/1.04  --gc_record_bc_elim                     false
% 0.94/1.04  
% 0.94/1.04  ------ Preprocessing Options
% 0.94/1.04  
% 0.94/1.04  --preprocessing_flag                    true
% 0.94/1.04  --time_out_prep_mult                    0.1
% 0.94/1.04  --splitting_mode                        input
% 0.94/1.04  --splitting_grd                         true
% 0.94/1.04  --splitting_cvd                         false
% 0.94/1.04  --splitting_cvd_svl                     false
% 0.94/1.04  --splitting_nvd                         32
% 0.94/1.04  --sub_typing                            true
% 0.94/1.04  --prep_gs_sim                           true
% 0.94/1.04  --prep_unflatten                        true
% 0.94/1.04  --prep_res_sim                          true
% 0.94/1.04  --prep_upred                            true
% 0.94/1.04  --prep_sem_filter                       exhaustive
% 0.94/1.04  --prep_sem_filter_out                   false
% 0.94/1.04  --pred_elim                             true
% 0.94/1.04  --res_sim_input                         true
% 0.94/1.04  --eq_ax_congr_red                       true
% 0.94/1.04  --pure_diseq_elim                       true
% 0.94/1.04  --brand_transform                       false
% 0.94/1.04  --non_eq_to_eq                          false
% 0.94/1.04  --prep_def_merge                        true
% 0.94/1.04  --prep_def_merge_prop_impl              false
% 0.94/1.04  --prep_def_merge_mbd                    true
% 0.94/1.04  --prep_def_merge_tr_red                 false
% 0.94/1.04  --prep_def_merge_tr_cl                  false
% 0.94/1.04  --smt_preprocessing                     true
% 0.94/1.04  --smt_ac_axioms                         fast
% 0.94/1.04  --preprocessed_out                      false
% 0.94/1.04  --preprocessed_stats                    false
% 0.94/1.04  
% 0.94/1.04  ------ Abstraction refinement Options
% 0.94/1.04  
% 0.94/1.04  --abstr_ref                             []
% 0.94/1.04  --abstr_ref_prep                        false
% 0.94/1.04  --abstr_ref_until_sat                   false
% 0.94/1.04  --abstr_ref_sig_restrict                funpre
% 0.94/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.94/1.04  --abstr_ref_under                       []
% 0.94/1.04  
% 0.94/1.04  ------ SAT Options
% 0.94/1.04  
% 0.94/1.04  --sat_mode                              false
% 0.94/1.04  --sat_fm_restart_options                ""
% 0.94/1.04  --sat_gr_def                            false
% 0.94/1.04  --sat_epr_types                         true
% 0.94/1.04  --sat_non_cyclic_types                  false
% 0.94/1.04  --sat_finite_models                     false
% 0.94/1.04  --sat_fm_lemmas                         false
% 0.94/1.04  --sat_fm_prep                           false
% 0.94/1.04  --sat_fm_uc_incr                        true
% 0.94/1.04  --sat_out_model                         small
% 0.94/1.04  --sat_out_clauses                       false
% 0.94/1.04  
% 0.94/1.04  ------ QBF Options
% 0.94/1.04  
% 0.94/1.04  --qbf_mode                              false
% 0.94/1.04  --qbf_elim_univ                         false
% 0.94/1.04  --qbf_dom_inst                          none
% 0.94/1.04  --qbf_dom_pre_inst                      false
% 0.94/1.04  --qbf_sk_in                             false
% 0.94/1.04  --qbf_pred_elim                         true
% 0.94/1.04  --qbf_split                             512
% 0.94/1.04  
% 0.94/1.04  ------ BMC1 Options
% 0.94/1.04  
% 0.94/1.04  --bmc1_incremental                      false
% 0.94/1.04  --bmc1_axioms                           reachable_all
% 0.94/1.04  --bmc1_min_bound                        0
% 0.94/1.04  --bmc1_max_bound                        -1
% 0.94/1.04  --bmc1_max_bound_default                -1
% 0.94/1.04  --bmc1_symbol_reachability              true
% 0.94/1.04  --bmc1_property_lemmas                  false
% 0.94/1.04  --bmc1_k_induction                      false
% 0.94/1.04  --bmc1_non_equiv_states                 false
% 0.94/1.04  --bmc1_deadlock                         false
% 0.94/1.04  --bmc1_ucm                              false
% 0.94/1.04  --bmc1_add_unsat_core                   none
% 0.94/1.04  --bmc1_unsat_core_children              false
% 0.94/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.94/1.04  --bmc1_out_stat                         full
% 0.94/1.04  --bmc1_ground_init                      false
% 0.94/1.04  --bmc1_pre_inst_next_state              false
% 0.94/1.04  --bmc1_pre_inst_state                   false
% 0.94/1.04  --bmc1_pre_inst_reach_state             false
% 0.94/1.04  --bmc1_out_unsat_core                   false
% 0.94/1.04  --bmc1_aig_witness_out                  false
% 0.94/1.04  --bmc1_verbose                          false
% 0.94/1.04  --bmc1_dump_clauses_tptp                false
% 0.94/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.94/1.04  --bmc1_dump_file                        -
% 0.94/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.94/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.94/1.04  --bmc1_ucm_extend_mode                  1
% 0.94/1.04  --bmc1_ucm_init_mode                    2
% 0.94/1.04  --bmc1_ucm_cone_mode                    none
% 0.94/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.94/1.04  --bmc1_ucm_relax_model                  4
% 0.94/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.94/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.94/1.04  --bmc1_ucm_layered_model                none
% 0.94/1.04  --bmc1_ucm_max_lemma_size               10
% 0.94/1.04  
% 0.94/1.04  ------ AIG Options
% 0.94/1.04  
% 0.94/1.04  --aig_mode                              false
% 0.94/1.04  
% 0.94/1.04  ------ Instantiation Options
% 0.94/1.04  
% 0.94/1.04  --instantiation_flag                    true
% 0.94/1.04  --inst_sos_flag                         false
% 0.94/1.04  --inst_sos_phase                        true
% 0.94/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.94/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.94/1.04  --inst_lit_sel_side                     num_symb
% 0.94/1.04  --inst_solver_per_active                1400
% 0.94/1.04  --inst_solver_calls_frac                1.
% 0.94/1.04  --inst_passive_queue_type               priority_queues
% 0.94/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.94/1.04  --inst_passive_queues_freq              [25;2]
% 0.94/1.04  --inst_dismatching                      true
% 0.94/1.04  --inst_eager_unprocessed_to_passive     true
% 0.94/1.04  --inst_prop_sim_given                   true
% 0.94/1.04  --inst_prop_sim_new                     false
% 0.94/1.04  --inst_subs_new                         false
% 0.94/1.04  --inst_eq_res_simp                      false
% 0.94/1.04  --inst_subs_given                       false
% 0.94/1.04  --inst_orphan_elimination               true
% 0.94/1.04  --inst_learning_loop_flag               true
% 0.94/1.04  --inst_learning_start                   3000
% 0.94/1.04  --inst_learning_factor                  2
% 0.94/1.04  --inst_start_prop_sim_after_learn       3
% 0.94/1.04  --inst_sel_renew                        solver
% 0.94/1.04  --inst_lit_activity_flag                true
% 0.94/1.04  --inst_restr_to_given                   false
% 0.94/1.04  --inst_activity_threshold               500
% 0.94/1.04  --inst_out_proof                        true
% 0.94/1.04  
% 0.94/1.04  ------ Resolution Options
% 0.94/1.04  
% 0.94/1.04  --resolution_flag                       true
% 0.94/1.04  --res_lit_sel                           adaptive
% 0.94/1.04  --res_lit_sel_side                      none
% 0.94/1.04  --res_ordering                          kbo
% 0.94/1.04  --res_to_prop_solver                    active
% 0.94/1.04  --res_prop_simpl_new                    false
% 0.94/1.04  --res_prop_simpl_given                  true
% 0.94/1.04  --res_passive_queue_type                priority_queues
% 0.94/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.94/1.04  --res_passive_queues_freq               [15;5]
% 0.94/1.04  --res_forward_subs                      full
% 0.94/1.04  --res_backward_subs                     full
% 0.94/1.04  --res_forward_subs_resolution           true
% 0.94/1.04  --res_backward_subs_resolution          true
% 0.94/1.04  --res_orphan_elimination                true
% 0.94/1.04  --res_time_limit                        2.
% 0.94/1.04  --res_out_proof                         true
% 0.94/1.04  
% 0.94/1.04  ------ Superposition Options
% 0.94/1.04  
% 0.94/1.04  --superposition_flag                    true
% 0.94/1.04  --sup_passive_queue_type                priority_queues
% 0.94/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.94/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.94/1.04  --demod_completeness_check              fast
% 0.94/1.04  --demod_use_ground                      true
% 0.94/1.04  --sup_to_prop_solver                    passive
% 0.94/1.04  --sup_prop_simpl_new                    true
% 0.94/1.04  --sup_prop_simpl_given                  true
% 0.94/1.04  --sup_fun_splitting                     false
% 0.94/1.04  --sup_smt_interval                      50000
% 0.94/1.04  
% 0.94/1.04  ------ Superposition Simplification Setup
% 0.94/1.04  
% 0.94/1.04  --sup_indices_passive                   []
% 0.94/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.94/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.04  --sup_full_bw                           [BwDemod]
% 0.94/1.04  --sup_immed_triv                        [TrivRules]
% 0.94/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.94/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.04  --sup_immed_bw_main                     []
% 0.94/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.94/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.04  
% 0.94/1.04  ------ Combination Options
% 0.94/1.04  
% 0.94/1.04  --comb_res_mult                         3
% 0.94/1.04  --comb_sup_mult                         2
% 0.94/1.04  --comb_inst_mult                        10
% 0.94/1.04  
% 0.94/1.04  ------ Debug Options
% 0.94/1.04  
% 0.94/1.04  --dbg_backtrace                         false
% 0.94/1.04  --dbg_dump_prop_clauses                 false
% 0.94/1.04  --dbg_dump_prop_clauses_file            -
% 0.94/1.04  --dbg_out_stat                          false
% 0.94/1.04  ------ Parsing...
% 0.94/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.94/1.04  
% 0.94/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.94/1.04  
% 0.94/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.94/1.04  
% 0.94/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.94/1.04  ------ Proving...
% 0.94/1.04  ------ Problem Properties 
% 0.94/1.04  
% 0.94/1.04  
% 0.94/1.04  clauses                                 16
% 0.94/1.04  conjectures                             12
% 0.94/1.04  EPR                                     9
% 0.94/1.04  Horn                                    12
% 0.94/1.04  unary                                   11
% 0.94/1.04  binary                                  0
% 0.94/1.04  lits                                    39
% 0.94/1.04  lits eq                                 33
% 0.94/1.04  fd_pure                                 0
% 0.94/1.04  fd_pseudo                               0
% 0.94/1.04  fd_cond                                 4
% 0.94/1.04  fd_pseudo_cond                          0
% 0.94/1.04  AC symbols                              0
% 0.94/1.04  
% 0.94/1.04  ------ Schedule dynamic 5 is on 
% 0.94/1.04  
% 0.94/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.94/1.04  
% 0.94/1.04  
% 0.94/1.04  ------ 
% 0.94/1.04  Current options:
% 0.94/1.04  ------ 
% 0.94/1.04  
% 0.94/1.04  ------ Input Options
% 0.94/1.04  
% 0.94/1.04  --out_options                           all
% 0.94/1.04  --tptp_safe_out                         true
% 0.94/1.04  --problem_path                          ""
% 0.94/1.04  --include_path                          ""
% 0.94/1.04  --clausifier                            res/vclausify_rel
% 0.94/1.04  --clausifier_options                    --mode clausify
% 0.94/1.04  --stdin                                 false
% 0.94/1.04  --stats_out                             all
% 0.94/1.04  
% 0.94/1.04  ------ General Options
% 0.94/1.04  
% 0.94/1.04  --fof                                   false
% 0.94/1.04  --time_out_real                         305.
% 0.94/1.04  --time_out_virtual                      -1.
% 0.94/1.04  --symbol_type_check                     false
% 0.94/1.04  --clausify_out                          false
% 0.94/1.04  --sig_cnt_out                           false
% 0.94/1.04  --trig_cnt_out                          false
% 0.94/1.04  --trig_cnt_out_tolerance                1.
% 0.94/1.04  --trig_cnt_out_sk_spl                   false
% 0.94/1.04  --abstr_cl_out                          false
% 0.94/1.04  
% 0.94/1.04  ------ Global Options
% 0.94/1.04  
% 0.94/1.04  --schedule                              default
% 0.94/1.04  --add_important_lit                     false
% 0.94/1.04  --prop_solver_per_cl                    1000
% 0.94/1.04  --min_unsat_core                        false
% 0.94/1.04  --soft_assumptions                      false
% 0.94/1.04  --soft_lemma_size                       3
% 0.94/1.04  --prop_impl_unit_size                   0
% 0.94/1.04  --prop_impl_unit                        []
% 0.94/1.04  --share_sel_clauses                     true
% 0.94/1.04  --reset_solvers                         false
% 0.94/1.04  --bc_imp_inh                            [conj_cone]
% 0.94/1.04  --conj_cone_tolerance                   3.
% 0.94/1.04  --extra_neg_conj                        none
% 0.94/1.04  --large_theory_mode                     true
% 0.94/1.04  --prolific_symb_bound                   200
% 0.94/1.04  --lt_threshold                          2000
% 0.94/1.04  --clause_weak_htbl                      true
% 0.94/1.04  --gc_record_bc_elim                     false
% 0.94/1.04  
% 0.94/1.04  ------ Preprocessing Options
% 0.94/1.04  
% 0.94/1.04  --preprocessing_flag                    true
% 0.94/1.04  --time_out_prep_mult                    0.1
% 0.94/1.04  --splitting_mode                        input
% 0.94/1.04  --splitting_grd                         true
% 0.94/1.04  --splitting_cvd                         false
% 0.94/1.04  --splitting_cvd_svl                     false
% 0.94/1.04  --splitting_nvd                         32
% 0.94/1.04  --sub_typing                            true
% 0.94/1.04  --prep_gs_sim                           true
% 0.94/1.04  --prep_unflatten                        true
% 0.94/1.04  --prep_res_sim                          true
% 0.94/1.04  --prep_upred                            true
% 0.94/1.04  --prep_sem_filter                       exhaustive
% 0.94/1.04  --prep_sem_filter_out                   false
% 0.94/1.04  --pred_elim                             true
% 0.94/1.04  --res_sim_input                         true
% 0.94/1.04  --eq_ax_congr_red                       true
% 0.94/1.04  --pure_diseq_elim                       true
% 0.94/1.04  --brand_transform                       false
% 0.94/1.04  --non_eq_to_eq                          false
% 0.94/1.04  --prep_def_merge                        true
% 0.94/1.04  --prep_def_merge_prop_impl              false
% 0.94/1.04  --prep_def_merge_mbd                    true
% 0.94/1.04  --prep_def_merge_tr_red                 false
% 0.94/1.04  --prep_def_merge_tr_cl                  false
% 0.94/1.04  --smt_preprocessing                     true
% 0.94/1.04  --smt_ac_axioms                         fast
% 0.94/1.04  --preprocessed_out                      false
% 0.94/1.04  --preprocessed_stats                    false
% 0.94/1.04  
% 0.94/1.04  ------ Abstraction refinement Options
% 0.94/1.04  
% 0.94/1.04  --abstr_ref                             []
% 0.94/1.04  --abstr_ref_prep                        false
% 0.94/1.04  --abstr_ref_until_sat                   false
% 0.94/1.04  --abstr_ref_sig_restrict                funpre
% 0.94/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.94/1.04  --abstr_ref_under                       []
% 0.94/1.04  
% 0.94/1.04  ------ SAT Options
% 0.94/1.04  
% 0.94/1.04  --sat_mode                              false
% 0.94/1.04  --sat_fm_restart_options                ""
% 0.94/1.04  --sat_gr_def                            false
% 0.94/1.04  --sat_epr_types                         true
% 0.94/1.04  --sat_non_cyclic_types                  false
% 0.94/1.04  --sat_finite_models                     false
% 0.94/1.04  --sat_fm_lemmas                         false
% 0.94/1.04  --sat_fm_prep                           false
% 0.94/1.04  --sat_fm_uc_incr                        true
% 0.94/1.04  --sat_out_model                         small
% 0.94/1.04  --sat_out_clauses                       false
% 0.94/1.04  
% 0.94/1.04  ------ QBF Options
% 0.94/1.04  
% 0.94/1.04  --qbf_mode                              false
% 0.94/1.04  --qbf_elim_univ                         false
% 0.94/1.04  --qbf_dom_inst                          none
% 0.94/1.04  --qbf_dom_pre_inst                      false
% 0.94/1.04  --qbf_sk_in                             false
% 0.94/1.04  --qbf_pred_elim                         true
% 0.94/1.04  --qbf_split                             512
% 0.94/1.04  
% 0.94/1.04  ------ BMC1 Options
% 0.94/1.04  
% 0.94/1.04  --bmc1_incremental                      false
% 0.94/1.04  --bmc1_axioms                           reachable_all
% 0.94/1.04  --bmc1_min_bound                        0
% 0.94/1.04  --bmc1_max_bound                        -1
% 0.94/1.04  --bmc1_max_bound_default                -1
% 0.94/1.04  --bmc1_symbol_reachability              true
% 0.94/1.04  --bmc1_property_lemmas                  false
% 0.94/1.04  --bmc1_k_induction                      false
% 0.94/1.04  --bmc1_non_equiv_states                 false
% 0.94/1.04  --bmc1_deadlock                         false
% 0.94/1.04  --bmc1_ucm                              false
% 0.94/1.04  --bmc1_add_unsat_core                   none
% 0.94/1.04  --bmc1_unsat_core_children              false
% 0.94/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.94/1.04  --bmc1_out_stat                         full
% 0.94/1.04  --bmc1_ground_init                      false
% 0.94/1.04  --bmc1_pre_inst_next_state              false
% 0.94/1.04  --bmc1_pre_inst_state                   false
% 0.94/1.04  --bmc1_pre_inst_reach_state             false
% 0.94/1.04  --bmc1_out_unsat_core                   false
% 0.94/1.04  --bmc1_aig_witness_out                  false
% 0.94/1.04  --bmc1_verbose                          false
% 0.94/1.04  --bmc1_dump_clauses_tptp                false
% 0.94/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.94/1.04  --bmc1_dump_file                        -
% 0.94/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.94/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.94/1.04  --bmc1_ucm_extend_mode                  1
% 0.94/1.04  --bmc1_ucm_init_mode                    2
% 0.94/1.04  --bmc1_ucm_cone_mode                    none
% 0.94/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.94/1.04  --bmc1_ucm_relax_model                  4
% 0.94/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.94/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.94/1.04  --bmc1_ucm_layered_model                none
% 0.94/1.04  --bmc1_ucm_max_lemma_size               10
% 0.94/1.04  
% 0.94/1.04  ------ AIG Options
% 0.94/1.04  
% 0.94/1.04  --aig_mode                              false
% 0.94/1.04  
% 0.94/1.04  ------ Instantiation Options
% 0.94/1.04  
% 0.94/1.04  --instantiation_flag                    true
% 0.94/1.04  --inst_sos_flag                         false
% 0.94/1.04  --inst_sos_phase                        true
% 0.94/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.94/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.94/1.04  --inst_lit_sel_side                     none
% 0.94/1.04  --inst_solver_per_active                1400
% 0.94/1.04  --inst_solver_calls_frac                1.
% 0.94/1.04  --inst_passive_queue_type               priority_queues
% 0.94/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.94/1.04  --inst_passive_queues_freq              [25;2]
% 0.94/1.04  --inst_dismatching                      true
% 0.94/1.04  --inst_eager_unprocessed_to_passive     true
% 0.94/1.04  --inst_prop_sim_given                   true
% 0.94/1.04  --inst_prop_sim_new                     false
% 0.94/1.04  --inst_subs_new                         false
% 0.94/1.04  --inst_eq_res_simp                      false
% 0.94/1.04  --inst_subs_given                       false
% 0.94/1.04  --inst_orphan_elimination               true
% 0.94/1.04  --inst_learning_loop_flag               true
% 0.94/1.04  --inst_learning_start                   3000
% 0.94/1.04  --inst_learning_factor                  2
% 0.94/1.04  --inst_start_prop_sim_after_learn       3
% 0.94/1.04  --inst_sel_renew                        solver
% 0.94/1.04  --inst_lit_activity_flag                true
% 0.94/1.04  --inst_restr_to_given                   false
% 0.94/1.04  --inst_activity_threshold               500
% 0.94/1.04  --inst_out_proof                        true
% 0.94/1.04  
% 0.94/1.04  ------ Resolution Options
% 0.94/1.04  
% 0.94/1.04  --resolution_flag                       false
% 0.94/1.04  --res_lit_sel                           adaptive
% 0.94/1.04  --res_lit_sel_side                      none
% 0.94/1.04  --res_ordering                          kbo
% 0.94/1.04  --res_to_prop_solver                    active
% 0.94/1.04  --res_prop_simpl_new                    false
% 0.94/1.04  --res_prop_simpl_given                  true
% 0.94/1.04  --res_passive_queue_type                priority_queues
% 0.94/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.94/1.04  --res_passive_queues_freq               [15;5]
% 0.94/1.04  --res_forward_subs                      full
% 0.94/1.04  --res_backward_subs                     full
% 0.94/1.04  --res_forward_subs_resolution           true
% 0.94/1.04  --res_backward_subs_resolution          true
% 0.94/1.04  --res_orphan_elimination                true
% 0.94/1.04  --res_time_limit                        2.
% 0.94/1.04  --res_out_proof                         true
% 0.94/1.04  
% 0.94/1.04  ------ Superposition Options
% 0.94/1.04  
% 0.94/1.04  --superposition_flag                    true
% 0.94/1.04  --sup_passive_queue_type                priority_queues
% 0.94/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.94/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.94/1.04  --demod_completeness_check              fast
% 0.94/1.04  --demod_use_ground                      true
% 0.94/1.04  --sup_to_prop_solver                    passive
% 0.94/1.04  --sup_prop_simpl_new                    true
% 0.94/1.04  --sup_prop_simpl_given                  true
% 0.94/1.04  --sup_fun_splitting                     false
% 0.94/1.04  --sup_smt_interval                      50000
% 0.94/1.04  
% 0.94/1.04  ------ Superposition Simplification Setup
% 0.94/1.04  
% 0.94/1.04  --sup_indices_passive                   []
% 0.94/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.94/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.04  --sup_full_bw                           [BwDemod]
% 0.94/1.04  --sup_immed_triv                        [TrivRules]
% 0.94/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.94/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.04  --sup_immed_bw_main                     []
% 0.94/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.94/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.04  
% 0.94/1.04  ------ Combination Options
% 0.94/1.04  
% 0.94/1.04  --comb_res_mult                         3
% 0.94/1.04  --comb_sup_mult                         2
% 0.94/1.04  --comb_inst_mult                        10
% 0.94/1.04  
% 0.94/1.04  ------ Debug Options
% 0.94/1.04  
% 0.94/1.04  --dbg_backtrace                         false
% 0.94/1.04  --dbg_dump_prop_clauses                 false
% 0.94/1.04  --dbg_dump_prop_clauses_file            -
% 0.94/1.04  --dbg_out_stat                          false
% 0.94/1.04  
% 0.94/1.04  
% 0.94/1.04  
% 0.94/1.04  
% 0.94/1.04  ------ Proving...
% 0.94/1.04  
% 0.94/1.04  
% 0.94/1.04  % SZS status Theorem for theBenchmark.p
% 0.94/1.04  
% 0.94/1.04   Resolution empty clause
% 0.94/1.04  
% 0.94/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.94/1.04  
% 0.94/1.04  fof(f2,conjecture,(
% 0.94/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ~(? [X8] : (? [X9] : (~(k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9) & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9) & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9) & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X7 & k1_xboole_0 != X6 & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.94/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.04  
% 0.94/1.04  fof(f3,negated_conjecture,(
% 0.94/1.04    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : ~(? [X8] : (? [X9] : (~(k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9) & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9) & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9) & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X7 & k1_xboole_0 != X6 & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.94/1.04    inference(negated_conjecture,[],[f2])).
% 0.94/1.04  
% 0.94/1.04  fof(f5,plain,(
% 0.94/1.04    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (? [X8] : (? [X9] : ((k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9) | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9) | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9) | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X7 & k1_xboole_0 != X6 & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.94/1.04    inference(ennf_transformation,[],[f3])).
% 0.94/1.04  
% 0.94/1.04  fof(f8,plain,(
% 0.94/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (? [X9] : ((k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9) | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9) | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9) | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) => ((k11_mcart_1(X4,X5,X6,X7,sK9) != k11_mcart_1(X0,X1,X2,X3,X8) | k10_mcart_1(X4,X5,X6,X7,sK9) != k10_mcart_1(X0,X1,X2,X3,X8) | k9_mcart_1(X4,X5,X6,X7,sK9) != k9_mcart_1(X0,X1,X2,X3,X8) | k8_mcart_1(X4,X5,X6,X7,sK9) != k8_mcart_1(X0,X1,X2,X3,X8)) & sK9 = X8 & m1_subset_1(sK9,k4_zfmisc_1(X4,X5,X6,X7)))) )),
% 0.94/1.04    introduced(choice_axiom,[])).
% 0.94/1.04  
% 0.94/1.04  fof(f7,plain,(
% 0.94/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (? [X8] : (? [X9] : ((k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9) | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9) | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9) | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) => (? [X9] : ((k11_mcart_1(X0,X1,X2,X3,sK8) != k11_mcart_1(X4,X5,X6,X7,X9) | k10_mcart_1(X0,X1,X2,X3,sK8) != k10_mcart_1(X4,X5,X6,X7,X9) | k9_mcart_1(X0,X1,X2,X3,sK8) != k9_mcart_1(X4,X5,X6,X7,X9) | k8_mcart_1(X0,X1,X2,X3,sK8) != k8_mcart_1(X4,X5,X6,X7,X9)) & sK8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 0.94/1.04    introduced(choice_axiom,[])).
% 0.94/1.04  
% 0.94/1.04  fof(f6,plain,(
% 0.94/1.04    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (? [X8] : (? [X9] : ((k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9) | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9) | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9) | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X7 & k1_xboole_0 != X6 & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X8] : (? [X9] : ((k11_mcart_1(sK0,sK1,sK2,sK3,X8) != k11_mcart_1(sK4,sK5,sK6,sK7,X9) | k10_mcart_1(sK0,sK1,sK2,sK3,X8) != k10_mcart_1(sK4,sK5,sK6,sK7,X9) | k9_mcart_1(sK0,sK1,sK2,sK3,X8) != k9_mcart_1(sK4,sK5,sK6,sK7,X9) | k8_mcart_1(sK0,sK1,sK2,sK3,X8) != k8_mcart_1(sK4,sK5,sK6,sK7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(sK4,sK5,sK6,sK7))) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.94/1.04    introduced(choice_axiom,[])).
% 0.94/1.04  
% 0.94/1.04  fof(f9,plain,(
% 0.94/1.04    (((k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9) | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9) | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9)) & sK8 = sK9 & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.94/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f5,f8,f7,f6])).
% 0.94/1.04  
% 0.94/1.04  fof(f22,plain,(
% 0.94/1.04    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f1,axiom,(
% 0.94/1.04    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.94/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.04  
% 0.94/1.04  fof(f4,plain,(
% 0.94/1.04    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.94/1.04    inference(ennf_transformation,[],[f1])).
% 0.94/1.04  
% 0.94/1.04  fof(f10,plain,(
% 0.94/1.04    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.94/1.04    inference(cnf_transformation,[],[f4])).
% 0.94/1.04  
% 0.94/1.04  fof(f14,plain,(
% 0.94/1.04    k1_xboole_0 != sK0),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f15,plain,(
% 0.94/1.04    k1_xboole_0 != sK1),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f16,plain,(
% 0.94/1.04    k1_xboole_0 != sK2),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f17,plain,(
% 0.94/1.04    k1_xboole_0 != sK3),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f12,plain,(
% 0.94/1.04    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.94/1.04    inference(cnf_transformation,[],[f4])).
% 0.94/1.04  
% 0.94/1.04  fof(f13,plain,(
% 0.94/1.04    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.94/1.04    inference(cnf_transformation,[],[f4])).
% 0.94/1.04  
% 0.94/1.04  fof(f25,plain,(
% 0.94/1.04    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9) | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9) | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9)),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f24,plain,(
% 0.94/1.04    sK8 = sK9),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f18,plain,(
% 0.94/1.04    k1_xboole_0 != sK4),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f19,plain,(
% 0.94/1.04    k1_xboole_0 != sK5),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f20,plain,(
% 0.94/1.04    k1_xboole_0 != sK6),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f21,plain,(
% 0.94/1.04    k1_xboole_0 != sK7),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f23,plain,(
% 0.94/1.04    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.94/1.04    inference(cnf_transformation,[],[f9])).
% 0.94/1.04  
% 0.94/1.04  fof(f11,plain,(
% 0.94/1.04    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.94/1.04    inference(cnf_transformation,[],[f4])).
% 0.94/1.04  
% 0.94/1.04  cnf(c_7,negated_conjecture,
% 0.94/1.04      ( m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
% 0.94/1.04      inference(cnf_transformation,[],[f22]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_417,plain,
% 0.94/1.04      ( m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) = iProver_top ),
% 0.94/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3,plain,
% 0.94/1.04      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 0.94/1.04      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 0.94/1.04      | k1_xboole_0 = X4
% 0.94/1.04      | k1_xboole_0 = X3
% 0.94/1.04      | k1_xboole_0 = X2
% 0.94/1.04      | k1_xboole_0 = X1 ),
% 0.94/1.04      inference(cnf_transformation,[],[f10]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_419,plain,
% 0.94/1.04      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 0.94/1.04      | k1_xboole_0 = X3
% 0.94/1.04      | k1_xboole_0 = X2
% 0.94/1.04      | k1_xboole_0 = X1
% 0.94/1.04      | k1_xboole_0 = X0
% 0.94/1.04      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 0.94/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3404,plain,
% 0.94/1.04      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 0.94/1.04      | sK3 = k1_xboole_0
% 0.94/1.04      | sK2 = k1_xboole_0
% 0.94/1.04      | sK1 = k1_xboole_0
% 0.94/1.04      | sK0 = k1_xboole_0 ),
% 0.94/1.04      inference(superposition,[status(thm)],[c_417,c_419]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_15,negated_conjecture,
% 0.94/1.04      ( k1_xboole_0 != sK0 ),
% 0.94/1.04      inference(cnf_transformation,[],[f14]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_14,negated_conjecture,
% 0.94/1.04      ( k1_xboole_0 != sK1 ),
% 0.94/1.04      inference(cnf_transformation,[],[f15]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_13,negated_conjecture,
% 0.94/1.04      ( k1_xboole_0 != sK2 ),
% 0.94/1.04      inference(cnf_transformation,[],[f16]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_12,negated_conjecture,
% 0.94/1.04      ( k1_xboole_0 != sK3 ),
% 0.94/1.04      inference(cnf_transformation,[],[f17]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_300,plain,( X0 = X0 ),theory(equality) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_319,plain,
% 0.94/1.04      ( k1_xboole_0 = k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_300]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_301,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_528,plain,
% 0.94/1.04      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_301]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_529,plain,
% 0.94/1.04      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_528]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_530,plain,
% 0.94/1.04      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_301]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_531,plain,
% 0.94/1.04      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_530]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_532,plain,
% 0.94/1.04      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_301]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_533,plain,
% 0.94/1.04      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_532]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_534,plain,
% 0.94/1.04      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_301]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_535,plain,
% 0.94/1.04      ( sK0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_534]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3455,plain,
% 0.94/1.04      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 0.94/1.04      inference(global_propositional_subsumption,
% 0.94/1.04                [status(thm)],
% 0.94/1.04                [c_3404,c_15,c_14,c_13,c_12,c_319,c_529,c_531,c_533,c_535]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_1,plain,
% 0.94/1.04      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 0.94/1.04      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 0.94/1.04      | k1_xboole_0 = X4
% 0.94/1.04      | k1_xboole_0 = X3
% 0.94/1.04      | k1_xboole_0 = X2
% 0.94/1.04      | k1_xboole_0 = X1 ),
% 0.94/1.04      inference(cnf_transformation,[],[f12]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_421,plain,
% 0.94/1.04      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 0.94/1.04      | k1_xboole_0 = X3
% 0.94/1.04      | k1_xboole_0 = X2
% 0.94/1.04      | k1_xboole_0 = X1
% 0.94/1.04      | k1_xboole_0 = X0
% 0.94/1.04      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 0.94/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_2244,plain,
% 0.94/1.04      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
% 0.94/1.04      | sK3 = k1_xboole_0
% 0.94/1.04      | sK2 = k1_xboole_0
% 0.94/1.04      | sK1 = k1_xboole_0
% 0.94/1.04      | sK0 = k1_xboole_0 ),
% 0.94/1.04      inference(superposition,[status(thm)],[c_417,c_421]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3326,plain,
% 0.94/1.04      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
% 0.94/1.04      inference(global_propositional_subsumption,
% 0.94/1.04                [status(thm)],
% 0.94/1.04                [c_2244,c_15,c_14,c_13,c_12,c_319,c_529,c_531,c_533,c_535]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_0,plain,
% 0.94/1.04      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 0.94/1.04      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 0.94/1.04      | k1_xboole_0 = X4
% 0.94/1.04      | k1_xboole_0 = X3
% 0.94/1.04      | k1_xboole_0 = X2
% 0.94/1.04      | k1_xboole_0 = X1 ),
% 0.94/1.04      inference(cnf_transformation,[],[f13]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_422,plain,
% 0.94/1.04      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 0.94/1.04      | k1_xboole_0 = X3
% 0.94/1.04      | k1_xboole_0 = X2
% 0.94/1.04      | k1_xboole_0 = X1
% 0.94/1.04      | k1_xboole_0 = X0
% 0.94/1.04      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 0.94/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_1755,plain,
% 0.94/1.04      ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
% 0.94/1.04      | sK3 = k1_xboole_0
% 0.94/1.04      | sK2 = k1_xboole_0
% 0.94/1.04      | sK1 = k1_xboole_0
% 0.94/1.04      | sK0 = k1_xboole_0 ),
% 0.94/1.04      inference(superposition,[status(thm)],[c_417,c_422]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_2684,plain,
% 0.94/1.04      ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
% 0.94/1.04      inference(global_propositional_subsumption,
% 0.94/1.04                [status(thm)],
% 0.94/1.04                [c_1755,c_15,c_14,c_13,c_12,c_319,c_529,c_531,c_533,c_535]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_4,negated_conjecture,
% 0.94/1.04      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9)
% 0.94/1.04      | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
% 0.94/1.04      | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
% 0.94/1.04      | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
% 0.94/1.04      inference(cnf_transformation,[],[f25]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_5,negated_conjecture,
% 0.94/1.04      ( sK8 = sK9 ),
% 0.94/1.04      inference(cnf_transformation,[],[f24]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_494,plain,
% 0.94/1.04      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k11_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
% 0.94/1.04      inference(light_normalisation,[status(thm)],[c_4,c_5]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_2687,plain,
% 0.94/1.04      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8) ),
% 0.94/1.04      inference(demodulation,[status(thm)],[c_2684,c_494]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_11,negated_conjecture,
% 0.94/1.04      ( k1_xboole_0 != sK4 ),
% 0.94/1.04      inference(cnf_transformation,[],[f18]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_10,negated_conjecture,
% 0.94/1.04      ( k1_xboole_0 != sK5 ),
% 0.94/1.04      inference(cnf_transformation,[],[f19]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_9,negated_conjecture,
% 0.94/1.04      ( k1_xboole_0 != sK6 ),
% 0.94/1.04      inference(cnf_transformation,[],[f20]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_8,negated_conjecture,
% 0.94/1.04      ( k1_xboole_0 != sK7 ),
% 0.94/1.04      inference(cnf_transformation,[],[f21]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_520,plain,
% 0.94/1.04      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_301]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_521,plain,
% 0.94/1.04      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_520]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_522,plain,
% 0.94/1.04      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_301]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_523,plain,
% 0.94/1.04      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_522]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_524,plain,
% 0.94/1.04      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_301]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_525,plain,
% 0.94/1.04      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_524]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_526,plain,
% 0.94/1.04      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_301]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_527,plain,
% 0.94/1.04      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.04      inference(instantiation,[status(thm)],[c_526]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_6,negated_conjecture,
% 0.94/1.04      ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
% 0.94/1.04      inference(cnf_transformation,[],[f23]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_418,plain,
% 0.94/1.04      ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) = iProver_top ),
% 0.94/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_443,plain,
% 0.94/1.04      ( m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) = iProver_top ),
% 0.94/1.04      inference(light_normalisation,[status(thm)],[c_418,c_5]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_1756,plain,
% 0.94/1.04      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
% 0.94/1.04      | sK7 = k1_xboole_0
% 0.94/1.04      | sK6 = k1_xboole_0
% 0.94/1.04      | sK5 = k1_xboole_0
% 0.94/1.04      | sK4 = k1_xboole_0 ),
% 0.94/1.04      inference(superposition,[status(thm)],[c_443,c_422]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_2688,plain,
% 0.94/1.04      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
% 0.94/1.04      inference(global_propositional_subsumption,
% 0.94/1.04                [status(thm)],
% 0.94/1.04                [c_2687,c_11,c_10,c_9,c_8,c_319,c_521,c_523,c_525,c_527,c_1756]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_2689,plain,
% 0.94/1.04      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
% 0.94/1.04      inference(renaming,[status(thm)],[c_2688]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3329,plain,
% 0.94/1.04      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8)) ),
% 0.94/1.04      inference(demodulation,[status(thm)],[c_3326,c_2689]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_2245,plain,
% 0.94/1.04      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
% 0.94/1.04      | sK7 = k1_xboole_0
% 0.94/1.04      | sK6 = k1_xboole_0
% 0.94/1.04      | sK5 = k1_xboole_0
% 0.94/1.04      | sK4 = k1_xboole_0 ),
% 0.94/1.04      inference(superposition,[status(thm)],[c_443,c_421]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3333,plain,
% 0.94/1.04      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
% 0.94/1.04      inference(global_propositional_subsumption,
% 0.94/1.04                [status(thm)],
% 0.94/1.04                [c_3329,c_11,c_10,c_9,c_8,c_319,c_521,c_523,c_525,c_527,c_2245]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3334,plain,
% 0.94/1.04      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8)
% 0.94/1.04      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
% 0.94/1.04      inference(renaming,[status(thm)],[c_3333]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3458,plain,
% 0.94/1.04      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 0.94/1.04      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
% 0.94/1.04      inference(demodulation,[status(thm)],[c_3455,c_3334]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3405,plain,
% 0.94/1.04      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 0.94/1.04      | sK7 = k1_xboole_0
% 0.94/1.04      | sK6 = k1_xboole_0
% 0.94/1.04      | sK5 = k1_xboole_0
% 0.94/1.04      | sK4 = k1_xboole_0 ),
% 0.94/1.04      inference(superposition,[status(thm)],[c_443,c_419]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3528,plain,
% 0.94/1.04      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8) ),
% 0.94/1.04      inference(global_propositional_subsumption,
% 0.94/1.04                [status(thm)],
% 0.94/1.04                [c_3458,c_11,c_10,c_9,c_8,c_319,c_521,c_523,c_525,c_527,c_3405]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_2,plain,
% 0.94/1.04      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 0.94/1.04      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 0.94/1.04      | k1_xboole_0 = X4
% 0.94/1.04      | k1_xboole_0 = X3
% 0.94/1.04      | k1_xboole_0 = X2
% 0.94/1.04      | k1_xboole_0 = X1 ),
% 0.94/1.04      inference(cnf_transformation,[],[f11]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_420,plain,
% 0.94/1.04      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 0.94/1.04      | k1_xboole_0 = X3
% 0.94/1.04      | k1_xboole_0 = X2
% 0.94/1.04      | k1_xboole_0 = X1
% 0.94/1.04      | k1_xboole_0 = X0
% 0.94/1.04      | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 0.94/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3433,plain,
% 0.94/1.04      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 0.94/1.04      | sK3 = k1_xboole_0
% 0.94/1.04      | sK2 = k1_xboole_0
% 0.94/1.04      | sK1 = k1_xboole_0
% 0.94/1.04      | sK0 = k1_xboole_0 ),
% 0.94/1.04      inference(superposition,[status(thm)],[c_417,c_420]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3462,plain,
% 0.94/1.04      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 0.94/1.04      inference(global_propositional_subsumption,
% 0.94/1.04                [status(thm)],
% 0.94/1.04                [c_3433,c_15,c_14,c_13,c_12,c_319,c_529,c_531,c_533,c_535]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3434,plain,
% 0.94/1.04      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 0.94/1.04      | sK7 = k1_xboole_0
% 0.94/1.04      | sK6 = k1_xboole_0
% 0.94/1.04      | sK5 = k1_xboole_0
% 0.94/1.04      | sK4 = k1_xboole_0 ),
% 0.94/1.04      inference(superposition,[status(thm)],[c_443,c_420]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3465,plain,
% 0.94/1.04      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 0.94/1.04      inference(global_propositional_subsumption,
% 0.94/1.04                [status(thm)],
% 0.94/1.04                [c_3434,c_11,c_10,c_9,c_8,c_319,c_521,c_523,c_525,c_527]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3530,plain,
% 0.94/1.04      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 0.94/1.04      inference(light_normalisation,[status(thm)],[c_3528,c_3462,c_3465]) ).
% 0.94/1.04  
% 0.94/1.04  cnf(c_3531,plain,
% 0.94/1.04      ( $false ),
% 0.94/1.04      inference(equality_resolution_simp,[status(thm)],[c_3530]) ).
% 0.94/1.04  
% 0.94/1.04  
% 0.94/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.94/1.04  
% 0.94/1.04  ------                               Statistics
% 0.94/1.04  
% 0.94/1.04  ------ General
% 0.94/1.04  
% 0.94/1.04  abstr_ref_over_cycles:                  0
% 0.94/1.04  abstr_ref_under_cycles:                 0
% 0.94/1.04  gc_basic_clause_elim:                   0
% 0.94/1.04  forced_gc_time:                         0
% 0.94/1.04  parsing_time:                           0.011
% 0.94/1.04  unif_index_cands_time:                  0.
% 0.94/1.04  unif_index_add_time:                    0.
% 0.94/1.04  orderings_time:                         0.
% 0.94/1.04  out_proof_time:                         0.007
% 0.94/1.04  total_time:                             0.141
% 0.94/1.04  num_of_symbols:                         47
% 0.94/1.04  num_of_terms:                           9991
% 0.94/1.04  
% 0.94/1.04  ------ Preprocessing
% 0.94/1.04  
% 0.94/1.04  num_of_splits:                          0
% 0.94/1.04  num_of_split_atoms:                     0
% 0.94/1.04  num_of_reused_defs:                     0
% 0.94/1.04  num_eq_ax_congr_red:                    0
% 0.94/1.04  num_of_sem_filtered_clauses:            1
% 0.94/1.04  num_of_subtypes:                        0
% 0.94/1.04  monotx_restored_types:                  0
% 0.94/1.04  sat_num_of_epr_types:                   0
% 0.94/1.04  sat_num_of_non_cyclic_types:            0
% 0.94/1.04  sat_guarded_non_collapsed_types:        0
% 0.94/1.04  num_pure_diseq_elim:                    0
% 0.94/1.04  simp_replaced_by:                       0
% 0.94/1.04  res_preprocessed:                       69
% 0.94/1.04  prep_upred:                             0
% 0.94/1.04  prep_unflattend:                        8
% 0.94/1.04  smt_new_axioms:                         0
% 0.94/1.04  pred_elim_cands:                        1
% 0.94/1.04  pred_elim:                              0
% 0.94/1.04  pred_elim_cl:                           0
% 0.94/1.04  pred_elim_cycles:                       1
% 0.94/1.04  merged_defs:                            0
% 0.94/1.04  merged_defs_ncl:                        0
% 0.94/1.04  bin_hyper_res:                          0
% 0.94/1.04  prep_cycles:                            3
% 0.94/1.04  pred_elim_time:                         0.004
% 0.94/1.04  splitting_time:                         0.
% 0.94/1.04  sem_filter_time:                        0.
% 0.94/1.04  monotx_time:                            0.
% 0.94/1.04  subtype_inf_time:                       0.
% 0.94/1.04  
% 0.94/1.04  ------ Problem properties
% 0.94/1.04  
% 0.94/1.04  clauses:                                16
% 0.94/1.04  conjectures:                            12
% 0.94/1.04  epr:                                    9
% 0.94/1.04  horn:                                   12
% 0.94/1.04  ground:                                 12
% 0.94/1.04  unary:                                  11
% 0.94/1.04  binary:                                 0
% 0.94/1.04  lits:                                   39
% 0.94/1.04  lits_eq:                                33
% 0.94/1.04  fd_pure:                                0
% 0.94/1.04  fd_pseudo:                              0
% 0.94/1.04  fd_cond:                                4
% 0.94/1.04  fd_pseudo_cond:                         0
% 0.94/1.04  ac_symbols:                             0
% 0.94/1.04  
% 0.94/1.04  ------ Propositional Solver
% 0.94/1.04  
% 0.94/1.04  prop_solver_calls:                      22
% 0.94/1.04  prop_fast_solver_calls:                 550
% 0.94/1.04  smt_solver_calls:                       0
% 0.94/1.04  smt_fast_solver_calls:                  0
% 0.94/1.04  prop_num_of_clauses:                    1642
% 0.94/1.04  prop_preprocess_simplified:             5478
% 0.94/1.04  prop_fo_subsumed:                       35
% 0.94/1.04  prop_solver_time:                       0.
% 0.94/1.04  smt_solver_time:                        0.
% 0.94/1.04  smt_fast_solver_time:                   0.
% 0.94/1.04  prop_fast_solver_time:                  0.
% 0.94/1.04  prop_unsat_core_time:                   0.
% 0.94/1.04  
% 0.94/1.04  ------ QBF
% 0.94/1.04  
% 0.94/1.04  qbf_q_res:                              0
% 0.94/1.04  qbf_num_tautologies:                    0
% 0.94/1.04  qbf_prep_cycles:                        0
% 0.94/1.04  
% 0.94/1.04  ------ BMC1
% 0.94/1.04  
% 0.94/1.04  bmc1_current_bound:                     -1
% 0.94/1.04  bmc1_last_solved_bound:                 -1
% 0.94/1.04  bmc1_unsat_core_size:                   -1
% 0.94/1.04  bmc1_unsat_core_parents_size:           -1
% 0.94/1.04  bmc1_merge_next_fun:                    0
% 0.94/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.94/1.04  
% 0.94/1.04  ------ Instantiation
% 0.94/1.04  
% 0.94/1.04  inst_num_of_clauses:                    548
% 0.94/1.04  inst_num_in_passive:                    376
% 0.94/1.04  inst_num_in_active:                     140
% 0.94/1.04  inst_num_in_unprocessed:                32
% 0.94/1.04  inst_num_of_loops:                      140
% 0.94/1.04  inst_num_of_learning_restarts:          0
% 0.94/1.04  inst_num_moves_active_passive:          0
% 0.94/1.04  inst_lit_activity:                      0
% 0.94/1.04  inst_lit_activity_moves:                0
% 0.94/1.04  inst_num_tautologies:                   0
% 0.94/1.04  inst_num_prop_implied:                  0
% 0.94/1.04  inst_num_existing_simplified:           0
% 0.94/1.04  inst_num_eq_res_simplified:             0
% 0.94/1.04  inst_num_child_elim:                    0
% 0.94/1.04  inst_num_of_dismatching_blockings:      1
% 0.94/1.04  inst_num_of_non_proper_insts:           498
% 0.94/1.04  inst_num_of_duplicates:                 0
% 0.94/1.04  inst_inst_num_from_inst_to_res:         0
% 0.94/1.04  inst_dismatching_checking_time:         0.
% 0.94/1.04  
% 0.94/1.04  ------ Resolution
% 0.94/1.04  
% 0.94/1.04  res_num_of_clauses:                     0
% 0.94/1.04  res_num_in_passive:                     0
% 0.94/1.04  res_num_in_active:                      0
% 0.94/1.04  res_num_of_loops:                       72
% 0.94/1.04  res_forward_subset_subsumed:            8
% 0.94/1.04  res_backward_subset_subsumed:           0
% 0.94/1.04  res_forward_subsumed:                   0
% 0.94/1.04  res_backward_subsumed:                  0
% 0.94/1.04  res_forward_subsumption_resolution:     0
% 0.94/1.04  res_backward_subsumption_resolution:    0
% 0.94/1.04  res_clause_to_clause_subsumption:       24
% 0.94/1.04  res_orphan_elimination:                 0
% 0.94/1.04  res_tautology_del:                      1
% 0.94/1.04  res_num_eq_res_simplified:              0
% 0.94/1.04  res_num_sel_changes:                    0
% 0.94/1.04  res_moves_from_active_to_pass:          0
% 0.94/1.04  
% 0.94/1.04  ------ Superposition
% 0.94/1.04  
% 0.94/1.04  sup_time_total:                         0.
% 0.94/1.04  sup_time_generating:                    0.
% 0.94/1.04  sup_time_sim_full:                      0.
% 0.94/1.04  sup_time_sim_immed:                     0.
% 0.94/1.04  
% 0.94/1.04  sup_num_of_clauses:                     23
% 0.94/1.04  sup_num_in_active:                      23
% 0.94/1.04  sup_num_in_passive:                     0
% 0.94/1.04  sup_num_of_loops:                       26
% 0.94/1.04  sup_fw_superposition:                   8
% 0.94/1.04  sup_bw_superposition:                   0
% 0.94/1.04  sup_immediate_simplified:               0
% 0.94/1.04  sup_given_eliminated:                   0
% 0.94/1.04  comparisons_done:                       0
% 0.94/1.04  comparisons_avoided:                    16
% 0.94/1.04  
% 0.94/1.04  ------ Simplifications
% 0.94/1.04  
% 0.94/1.04  
% 0.94/1.04  sim_fw_subset_subsumed:                 0
% 0.94/1.04  sim_bw_subset_subsumed:                 0
% 0.94/1.04  sim_fw_subsumed:                        0
% 0.94/1.04  sim_bw_subsumed:                        0
% 0.94/1.04  sim_fw_subsumption_res:                 0
% 0.94/1.04  sim_bw_subsumption_res:                 0
% 0.94/1.04  sim_tautology_del:                      0
% 0.94/1.04  sim_eq_tautology_del:                   0
% 0.94/1.04  sim_eq_res_simp:                        0
% 0.94/1.04  sim_fw_demodulated:                     0
% 0.94/1.04  sim_bw_demodulated:                     3
% 0.94/1.04  sim_light_normalised:                   3
% 0.94/1.04  sim_joinable_taut:                      0
% 0.94/1.04  sim_joinable_simp:                      0
% 0.94/1.04  sim_ac_normalised:                      0
% 0.94/1.04  sim_smt_subsumption:                    0
% 0.94/1.04  
%------------------------------------------------------------------------------
