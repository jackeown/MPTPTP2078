%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0926+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:26 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
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
