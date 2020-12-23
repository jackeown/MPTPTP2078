%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:56 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  108 (1589 expanded)
%              Number of clauses        :   74 ( 582 expanded)
%              Number of leaves         :   11 ( 443 expanded)
%              Depth                    :   25
%              Number of atoms          :  500 (11143 expanded)
%              Number of equality atoms :  389 (7078 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k5_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X5
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k5_mcart_1(sK6,sK7,sK8,sK10) != sK9
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK9 = X5
                  | k3_mcart_1(X5,X6,X7) != sK10
                  | ~ m1_subset_1(X7,sK8) )
              | ~ m1_subset_1(X6,sK7) )
          | ~ m1_subset_1(X5,sK6) )
      & m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k5_mcart_1(sK6,sK7,sK8,sK10) != sK9
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK9 = X5
                | k3_mcart_1(X5,X6,X7) != sK10
                | ~ m1_subset_1(X7,sK8) )
            | ~ m1_subset_1(X6,sK7) )
        | ~ m1_subset_1(X5,sK6) )
    & m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f10,f19])).

fof(f31,plain,(
    m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X4,X5,X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(X4,X5,X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(X4,X5,sK5(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK5(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(X4,X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(X4,sK4(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK4(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK3(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK3(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK5(X0,X1,X2,X3),X2)
            & m1_subset_1(sK4(X0,X1,X2,X3),X1)
            & m1_subset_1(sK3(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f7,f17,f16,f15])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k5_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X5 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k5_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X5
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X5
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X5
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK0(X3,X4) != X4
        & k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK0(X3,X4) != X4
                    & k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X6,X7,X5] :
      ( sK9 = X5
      | k3_mcart_1(X5,X6,X7) != sK10
      | ~ m1_subset_1(X7,sK8)
      | ~ m1_subset_1(X6,sK7)
      | ~ m1_subset_1(X5,sK6) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    k5_mcart_1(sK6,sK7,sK8,sK10) != sK9 ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | sK0(X3,X4) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_264,plain,
    ( m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(sK3(X1,X2,X3,X0),X1)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_266,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
    | m1_subset_1(sK3(X1,X0,X2,X3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k3_zfmisc_1(X1,X3,X4))
    | k5_mcart_1(X1,X3,X4,X2) = X0
    | k3_mcart_1(sK0(X2,X0),sK1(X2,X0),sK2(X2,X0)) = X2
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_271,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2183,plain,
    ( k5_mcart_1(sK6,sK7,sK8,sK10) = X0
    | k3_mcart_1(sK0(sK10,X0),sK1(sK10,X0),sK2(sK10,X0)) = sK10
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_264,c_271])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_113,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_124,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_114,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_406,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_407,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_408,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_409,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_410,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_411,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_2266,plain,
    ( k3_mcart_1(sK0(sK10,X0),sK1(sK10,X0),sK2(sK10,X0)) = sK10
    | k5_mcart_1(sK6,sK7,sK8,sK10) = X0
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2183,c_13,c_12,c_11,c_124,c_407,c_409,c_411])).

cnf(c_2267,plain,
    ( k5_mcart_1(sK6,sK7,sK8,sK10) = X0
    | k3_mcart_1(sK0(sK10,X0),sK1(sK10,X0),sK2(sK10,X0)) = sK10
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_2266])).

cnf(c_2275,plain,
    ( sK3(sK6,X0,X1,X2) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | k3_mcart_1(sK0(sK10,sK3(sK6,X0,X1,X2)),sK1(sK10,sK3(sK6,X0,X1,X2)),sK2(sK10,sK3(sK6,X0,X1,X2))) = sK10
    | sK6 = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X2,k3_zfmisc_1(sK6,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_266,c_2267])).

cnf(c_2338,plain,
    ( k3_mcart_1(sK0(sK10,sK3(sK6,X0,X1,X2)),sK1(sK10,sK3(sK6,X0,X1,X2)),sK2(sK10,sK3(sK6,X0,X1,X2))) = sK10
    | sK3(sK6,X0,X1,X2) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X2,k3_zfmisc_1(sK6,X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2275,c_13,c_124,c_411])).

cnf(c_2339,plain,
    ( sK3(sK6,X0,X1,X2) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | k3_mcart_1(sK0(sK10,sK3(sK6,X0,X1,X2)),sK1(sK10,sK3(sK6,X0,X1,X2)),sK2(sK10,sK3(sK6,X0,X1,X2))) = sK10
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X2,k3_zfmisc_1(sK6,X0,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2338])).

cnf(c_2347,plain,
    ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | k3_mcart_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK2(sK10,sK3(sK6,sK7,sK8,sK10))) = sK10
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_264,c_2339])).

cnf(c_2410,plain,
    ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | k3_mcart_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK2(sK10,sK3(sK6,sK7,sK8,sK10))) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2347,c_12,c_11,c_124,c_407,c_409])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k3_mcart_1(sK3(X1,X2,X3,X0),sK4(X1,X2,X3,X0),sK5(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_269,plain,
    ( k3_mcart_1(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1162,plain,
    ( k3_mcart_1(sK3(sK6,sK7,sK8,sK10),sK4(sK6,sK7,sK8,sK10),sK5(sK6,sK7,sK8,sK10)) = sK10
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_264,c_269])).

cnf(c_1225,plain,
    ( k3_mcart_1(sK3(sK6,sK7,sK8,sK10),sK4(sK6,sK7,sK8,sK10),sK5(sK6,sK7,sK8,sK10)) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1162,c_13,c_12,c_11,c_124,c_407,c_409,c_411])).

cnf(c_7,plain,
    ( X0 = X1
    | k3_mcart_1(X2,X3,X0) != k3_mcart_1(X4,X5,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1229,plain,
    ( sK5(sK6,sK7,sK8,sK10) = X0
    | k3_mcart_1(X1,X2,X0) != sK10 ),
    inference(superposition,[status(thm)],[c_1225,c_7])).

cnf(c_2424,plain,
    ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | sK2(sK10,sK3(sK6,sK7,sK8,sK10)) = sK5(sK6,sK7,sK8,sK10) ),
    inference(superposition,[status(thm)],[c_2410,c_1229])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(X0,sK8)
    | ~ m1_subset_1(X1,sK7)
    | ~ m1_subset_1(X2,sK6)
    | k3_mcart_1(X2,X1,X0) != sK10
    | sK9 = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_265,plain,
    ( k3_mcart_1(X0,X1,X2) != sK10
    | sK9 = X0
    | m1_subset_1(X2,sK8) != iProver_top
    | m1_subset_1(X1,sK7) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2416,plain,
    ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK9
    | m1_subset_1(sK2(sK10,sK3(sK6,sK7,sK8,sK10)),sK8) != iProver_top
    | m1_subset_1(sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK7) != iProver_top
    | m1_subset_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_265])).

cnf(c_2553,plain,
    ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK9
    | m1_subset_1(sK5(sK6,sK7,sK8,sK10),sK8) != iProver_top
    | m1_subset_1(sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK7) != iProver_top
    | m1_subset_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2424,c_2416])).

cnf(c_16,plain,
    ( m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(sK5(X1,X2,X3,X0),X3)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,sK8))
    | m1_subset_1(sK5(X1,X2,sK8,X0),sK8)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK7,sK8))
    | m1_subset_1(sK5(X1,sK7,sK8,X0),sK8)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_967,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(sK6,sK7,sK8))
    | m1_subset_1(sK5(sK6,sK7,sK8,X0),sK8)
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_2317,plain,
    ( m1_subset_1(sK5(sK6,sK7,sK8,sK10),sK8)
    | ~ m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_2318,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | m1_subset_1(sK5(sK6,sK7,sK8,sK10),sK8) = iProver_top
    | m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2317])).

cnf(c_3809,plain,
    ( sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK9
    | sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | m1_subset_1(sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK7) != iProver_top
    | m1_subset_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2553,c_16,c_13,c_12,c_11,c_2318])).

cnf(c_3810,plain,
    ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK9
    | m1_subset_1(sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK7) != iProver_top
    | m1_subset_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3809])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(sK4(X1,X2,X3,X0),X2)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_267,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
    | m1_subset_1(sK4(X1,X0,X2,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_268,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
    | m1_subset_1(sK5(X1,X0,X2,X3),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1228,plain,
    ( sK3(sK6,sK7,sK8,sK10) = sK9
    | m1_subset_1(sK5(sK6,sK7,sK8,sK10),sK8) != iProver_top
    | m1_subset_1(sK4(sK6,sK7,sK8,sK10),sK7) != iProver_top
    | m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_265])).

cnf(c_1428,plain,
    ( sK3(sK6,sK7,sK8,sK10) = sK9
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | m1_subset_1(sK4(sK6,sK7,sK8,sK10),sK7) != iProver_top
    | m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top
    | m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_268,c_1228])).

cnf(c_2328,plain,
    ( m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top
    | m1_subset_1(sK4(sK6,sK7,sK8,sK10),sK7) != iProver_top
    | sK3(sK6,sK7,sK8,sK10) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1428,c_16,c_13,c_12,c_11,c_124,c_407,c_409,c_411])).

cnf(c_2329,plain,
    ( sK3(sK6,sK7,sK8,sK10) = sK9
    | m1_subset_1(sK4(sK6,sK7,sK8,sK10),sK7) != iProver_top
    | m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_2328])).

cnf(c_2335,plain,
    ( sK3(sK6,sK7,sK8,sK10) = sK9
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top
    | m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_267,c_2329])).

cnf(c_2336,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6)
    | ~ m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))
    | sK3(sK6,sK7,sK8,sK10) = sK9
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2335])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,sK8))
    | m1_subset_1(sK3(X1,X2,sK8,X0),X1)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK7,sK8))
    | m1_subset_1(sK3(X1,sK7,sK8,X0),X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_1388,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(sK6,sK7,sK8))
    | m1_subset_1(sK3(sK6,sK7,sK8,X0),sK6)
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_2698,plain,
    ( m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6)
    | ~ m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_2702,plain,
    ( sK3(sK6,sK7,sK8,sK10) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2335,c_15,c_13,c_12,c_11,c_124,c_407,c_409,c_411,c_2336,c_2698])).

cnf(c_3813,plain,
    ( k5_mcart_1(sK6,sK7,sK8,sK10) = sK9
    | sK0(sK10,sK9) = sK9
    | m1_subset_1(sK1(sK10,sK9),sK7) != iProver_top
    | m1_subset_1(sK0(sK10,sK9),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3810,c_2702])).

cnf(c_10,negated_conjecture,
    ( k5_mcart_1(sK6,sK7,sK8,sK10) != sK9 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3818,plain,
    ( sK0(sK10,sK9) = sK9
    | m1_subset_1(sK1(sK10,sK9),sK7) != iProver_top
    | m1_subset_1(sK0(sK10,sK9),sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3813,c_10])).

cnf(c_9,plain,
    ( X0 = X1
    | k3_mcart_1(X0,X2,X3) != k3_mcart_1(X1,X4,X5) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1233,plain,
    ( sK3(sK6,sK7,sK8,sK10) = X0
    | k3_mcart_1(X0,X1,X2) != sK10 ),
    inference(superposition,[status(thm)],[c_1225,c_9])).

cnf(c_2415,plain,
    ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
    | sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK3(sK6,sK7,sK8,sK10) ),
    inference(superposition,[status(thm)],[c_2410,c_1233])).

cnf(c_2710,plain,
    ( k5_mcart_1(sK6,sK7,sK8,sK10) = sK9
    | sK0(sK10,sK9) = sK9 ),
    inference(demodulation,[status(thm)],[c_2702,c_2415])).

cnf(c_3820,plain,
    ( sK0(sK10,sK9) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3818,c_10,c_2710])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k3_zfmisc_1(X1,X3,X4))
    | k5_mcart_1(X1,X3,X4,X2) = X0
    | sK0(X2,X0) != X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_272,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | sK0(X3,X4) != X4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3829,plain,
    ( k5_mcart_1(X0,X1,X2,sK10) = sK9
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK9,X0) != iProver_top
    | m1_subset_1(sK10,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_272])).

cnf(c_4146,plain,
    ( k5_mcart_1(sK6,sK7,sK8,sK10) = sK9
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | m1_subset_1(sK9,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_264,c_3829])).

cnf(c_2783,plain,
    ( sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | m1_subset_1(sK9,sK6) = iProver_top
    | m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_266])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4146,c_2783,c_411,c_409,c_407,c_124,c_10,c_11,c_12,c_13,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:38:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.19/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/0.98  
% 2.19/0.98  ------  iProver source info
% 2.19/0.98  
% 2.19/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.19/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/0.98  git: non_committed_changes: false
% 2.19/0.98  git: last_make_outside_of_git: false
% 2.19/0.98  
% 2.19/0.98  ------ 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options
% 2.19/0.98  
% 2.19/0.98  --out_options                           all
% 2.19/0.98  --tptp_safe_out                         true
% 2.19/0.98  --problem_path                          ""
% 2.19/0.98  --include_path                          ""
% 2.19/0.98  --clausifier                            res/vclausify_rel
% 2.19/0.98  --clausifier_options                    --mode clausify
% 2.19/0.98  --stdin                                 false
% 2.19/0.98  --stats_out                             all
% 2.19/0.98  
% 2.19/0.98  ------ General Options
% 2.19/0.98  
% 2.19/0.98  --fof                                   false
% 2.19/0.98  --time_out_real                         305.
% 2.19/0.98  --time_out_virtual                      -1.
% 2.19/0.98  --symbol_type_check                     false
% 2.19/0.98  --clausify_out                          false
% 2.19/0.98  --sig_cnt_out                           false
% 2.19/0.98  --trig_cnt_out                          false
% 2.19/0.98  --trig_cnt_out_tolerance                1.
% 2.19/0.98  --trig_cnt_out_sk_spl                   false
% 2.19/0.98  --abstr_cl_out                          false
% 2.19/0.98  
% 2.19/0.98  ------ Global Options
% 2.19/0.98  
% 2.19/0.98  --schedule                              default
% 2.19/0.98  --add_important_lit                     false
% 2.19/0.98  --prop_solver_per_cl                    1000
% 2.19/0.98  --min_unsat_core                        false
% 2.19/0.98  --soft_assumptions                      false
% 2.19/0.98  --soft_lemma_size                       3
% 2.19/0.98  --prop_impl_unit_size                   0
% 2.19/0.98  --prop_impl_unit                        []
% 2.19/0.98  --share_sel_clauses                     true
% 2.19/0.98  --reset_solvers                         false
% 2.19/0.98  --bc_imp_inh                            [conj_cone]
% 2.19/0.98  --conj_cone_tolerance                   3.
% 2.19/0.98  --extra_neg_conj                        none
% 2.19/0.98  --large_theory_mode                     true
% 2.19/0.98  --prolific_symb_bound                   200
% 2.19/0.98  --lt_threshold                          2000
% 2.19/0.98  --clause_weak_htbl                      true
% 2.19/0.98  --gc_record_bc_elim                     false
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing Options
% 2.19/0.98  
% 2.19/0.98  --preprocessing_flag                    true
% 2.19/0.98  --time_out_prep_mult                    0.1
% 2.19/0.98  --splitting_mode                        input
% 2.19/0.98  --splitting_grd                         true
% 2.19/0.98  --splitting_cvd                         false
% 2.19/0.98  --splitting_cvd_svl                     false
% 2.19/0.98  --splitting_nvd                         32
% 2.19/0.98  --sub_typing                            true
% 2.19/0.98  --prep_gs_sim                           true
% 2.19/0.98  --prep_unflatten                        true
% 2.19/0.98  --prep_res_sim                          true
% 2.19/0.98  --prep_upred                            true
% 2.19/0.98  --prep_sem_filter                       exhaustive
% 2.19/0.98  --prep_sem_filter_out                   false
% 2.19/0.98  --pred_elim                             true
% 2.19/0.98  --res_sim_input                         true
% 2.19/0.98  --eq_ax_congr_red                       true
% 2.19/0.98  --pure_diseq_elim                       true
% 2.19/0.98  --brand_transform                       false
% 2.19/0.98  --non_eq_to_eq                          false
% 2.19/0.98  --prep_def_merge                        true
% 2.19/0.98  --prep_def_merge_prop_impl              false
% 2.19/0.98  --prep_def_merge_mbd                    true
% 2.19/0.98  --prep_def_merge_tr_red                 false
% 2.19/0.98  --prep_def_merge_tr_cl                  false
% 2.19/0.98  --smt_preprocessing                     true
% 2.19/0.98  --smt_ac_axioms                         fast
% 2.19/0.98  --preprocessed_out                      false
% 2.19/0.98  --preprocessed_stats                    false
% 2.19/0.98  
% 2.19/0.98  ------ Abstraction refinement Options
% 2.19/0.98  
% 2.19/0.98  --abstr_ref                             []
% 2.19/0.98  --abstr_ref_prep                        false
% 2.19/0.98  --abstr_ref_until_sat                   false
% 2.19/0.98  --abstr_ref_sig_restrict                funpre
% 2.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.98  --abstr_ref_under                       []
% 2.19/0.98  
% 2.19/0.98  ------ SAT Options
% 2.19/0.98  
% 2.19/0.98  --sat_mode                              false
% 2.19/0.98  --sat_fm_restart_options                ""
% 2.19/0.98  --sat_gr_def                            false
% 2.19/0.98  --sat_epr_types                         true
% 2.19/0.98  --sat_non_cyclic_types                  false
% 2.19/0.98  --sat_finite_models                     false
% 2.19/0.98  --sat_fm_lemmas                         false
% 2.19/0.98  --sat_fm_prep                           false
% 2.19/0.98  --sat_fm_uc_incr                        true
% 2.19/0.98  --sat_out_model                         small
% 2.19/0.98  --sat_out_clauses                       false
% 2.19/0.98  
% 2.19/0.98  ------ QBF Options
% 2.19/0.98  
% 2.19/0.98  --qbf_mode                              false
% 2.19/0.98  --qbf_elim_univ                         false
% 2.19/0.98  --qbf_dom_inst                          none
% 2.19/0.98  --qbf_dom_pre_inst                      false
% 2.19/0.98  --qbf_sk_in                             false
% 2.19/0.98  --qbf_pred_elim                         true
% 2.19/0.98  --qbf_split                             512
% 2.19/0.98  
% 2.19/0.98  ------ BMC1 Options
% 2.19/0.98  
% 2.19/0.98  --bmc1_incremental                      false
% 2.19/0.98  --bmc1_axioms                           reachable_all
% 2.19/0.98  --bmc1_min_bound                        0
% 2.19/0.98  --bmc1_max_bound                        -1
% 2.19/0.98  --bmc1_max_bound_default                -1
% 2.19/0.98  --bmc1_symbol_reachability              true
% 2.19/0.98  --bmc1_property_lemmas                  false
% 2.19/0.98  --bmc1_k_induction                      false
% 2.19/0.98  --bmc1_non_equiv_states                 false
% 2.19/0.98  --bmc1_deadlock                         false
% 2.19/0.98  --bmc1_ucm                              false
% 2.19/0.98  --bmc1_add_unsat_core                   none
% 2.19/0.98  --bmc1_unsat_core_children              false
% 2.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.98  --bmc1_out_stat                         full
% 2.19/0.98  --bmc1_ground_init                      false
% 2.19/0.98  --bmc1_pre_inst_next_state              false
% 2.19/0.98  --bmc1_pre_inst_state                   false
% 2.19/0.98  --bmc1_pre_inst_reach_state             false
% 2.19/0.98  --bmc1_out_unsat_core                   false
% 2.19/0.98  --bmc1_aig_witness_out                  false
% 2.19/0.98  --bmc1_verbose                          false
% 2.19/0.98  --bmc1_dump_clauses_tptp                false
% 2.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.98  --bmc1_dump_file                        -
% 2.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.98  --bmc1_ucm_extend_mode                  1
% 2.19/0.98  --bmc1_ucm_init_mode                    2
% 2.19/0.98  --bmc1_ucm_cone_mode                    none
% 2.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.98  --bmc1_ucm_relax_model                  4
% 2.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.98  --bmc1_ucm_layered_model                none
% 2.19/0.98  --bmc1_ucm_max_lemma_size               10
% 2.19/0.98  
% 2.19/0.98  ------ AIG Options
% 2.19/0.98  
% 2.19/0.98  --aig_mode                              false
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation Options
% 2.19/0.98  
% 2.19/0.98  --instantiation_flag                    true
% 2.19/0.98  --inst_sos_flag                         false
% 2.19/0.98  --inst_sos_phase                        true
% 2.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel_side                     num_symb
% 2.19/0.98  --inst_solver_per_active                1400
% 2.19/0.98  --inst_solver_calls_frac                1.
% 2.19/0.98  --inst_passive_queue_type               priority_queues
% 2.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.98  --inst_passive_queues_freq              [25;2]
% 2.19/0.98  --inst_dismatching                      true
% 2.19/0.98  --inst_eager_unprocessed_to_passive     true
% 2.19/0.98  --inst_prop_sim_given                   true
% 2.19/0.98  --inst_prop_sim_new                     false
% 2.19/0.98  --inst_subs_new                         false
% 2.19/0.98  --inst_eq_res_simp                      false
% 2.19/0.98  --inst_subs_given                       false
% 2.19/0.98  --inst_orphan_elimination               true
% 2.19/0.98  --inst_learning_loop_flag               true
% 2.19/0.98  --inst_learning_start                   3000
% 2.19/0.98  --inst_learning_factor                  2
% 2.19/0.98  --inst_start_prop_sim_after_learn       3
% 2.19/0.98  --inst_sel_renew                        solver
% 2.19/0.98  --inst_lit_activity_flag                true
% 2.19/0.98  --inst_restr_to_given                   false
% 2.19/0.98  --inst_activity_threshold               500
% 2.19/0.98  --inst_out_proof                        true
% 2.19/0.98  
% 2.19/0.98  ------ Resolution Options
% 2.19/0.98  
% 2.19/0.98  --resolution_flag                       true
% 2.19/0.98  --res_lit_sel                           adaptive
% 2.19/0.98  --res_lit_sel_side                      none
% 2.19/0.98  --res_ordering                          kbo
% 2.19/0.98  --res_to_prop_solver                    active
% 2.19/0.98  --res_prop_simpl_new                    false
% 2.19/0.98  --res_prop_simpl_given                  true
% 2.19/0.98  --res_passive_queue_type                priority_queues
% 2.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.98  --res_passive_queues_freq               [15;5]
% 2.19/0.98  --res_forward_subs                      full
% 2.19/0.98  --res_backward_subs                     full
% 2.19/0.98  --res_forward_subs_resolution           true
% 2.19/0.98  --res_backward_subs_resolution          true
% 2.19/0.98  --res_orphan_elimination                true
% 2.19/0.98  --res_time_limit                        2.
% 2.19/0.98  --res_out_proof                         true
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Options
% 2.19/0.98  
% 2.19/0.98  --superposition_flag                    true
% 2.19/0.98  --sup_passive_queue_type                priority_queues
% 2.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.98  --demod_completeness_check              fast
% 2.19/0.98  --demod_use_ground                      true
% 2.19/0.98  --sup_to_prop_solver                    passive
% 2.19/0.98  --sup_prop_simpl_new                    true
% 2.19/0.98  --sup_prop_simpl_given                  true
% 2.19/0.98  --sup_fun_splitting                     false
% 2.19/0.98  --sup_smt_interval                      50000
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Simplification Setup
% 2.19/0.98  
% 2.19/0.98  --sup_indices_passive                   []
% 2.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_full_bw                           [BwDemod]
% 2.19/0.98  --sup_immed_triv                        [TrivRules]
% 2.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_immed_bw_main                     []
% 2.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  
% 2.19/0.98  ------ Combination Options
% 2.19/0.98  
% 2.19/0.98  --comb_res_mult                         3
% 2.19/0.98  --comb_sup_mult                         2
% 2.19/0.98  --comb_inst_mult                        10
% 2.19/0.98  
% 2.19/0.98  ------ Debug Options
% 2.19/0.98  
% 2.19/0.98  --dbg_backtrace                         false
% 2.19/0.98  --dbg_dump_prop_clauses                 false
% 2.19/0.98  --dbg_dump_prop_clauses_file            -
% 2.19/0.98  --dbg_out_stat                          false
% 2.19/0.98  ------ Parsing...
% 2.19/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/0.98  ------ Proving...
% 2.19/0.98  ------ Problem Properties 
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  clauses                                 16
% 2.19/0.98  conjectures                             6
% 2.19/0.98  EPR                                     3
% 2.19/0.98  Horn                                    9
% 2.19/0.98  unary                                   5
% 2.19/0.98  binary                                  3
% 2.19/0.98  lits                                    56
% 2.19/0.98  lits eq                                 39
% 2.19/0.98  fd_pure                                 0
% 2.19/0.98  fd_pseudo                               0
% 2.19/0.98  fd_cond                                 4
% 2.19/0.98  fd_pseudo_cond                          4
% 2.19/0.98  AC symbols                              0
% 2.19/0.98  
% 2.19/0.98  ------ Schedule dynamic 5 is on 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  ------ 
% 2.19/0.98  Current options:
% 2.19/0.98  ------ 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options
% 2.19/0.98  
% 2.19/0.98  --out_options                           all
% 2.19/0.98  --tptp_safe_out                         true
% 2.19/0.98  --problem_path                          ""
% 2.19/0.98  --include_path                          ""
% 2.19/0.98  --clausifier                            res/vclausify_rel
% 2.19/0.98  --clausifier_options                    --mode clausify
% 2.19/0.98  --stdin                                 false
% 2.19/0.98  --stats_out                             all
% 2.19/0.98  
% 2.19/0.98  ------ General Options
% 2.19/0.98  
% 2.19/0.98  --fof                                   false
% 2.19/0.98  --time_out_real                         305.
% 2.19/0.98  --time_out_virtual                      -1.
% 2.19/0.98  --symbol_type_check                     false
% 2.19/0.98  --clausify_out                          false
% 2.19/0.98  --sig_cnt_out                           false
% 2.19/0.98  --trig_cnt_out                          false
% 2.19/0.98  --trig_cnt_out_tolerance                1.
% 2.19/0.98  --trig_cnt_out_sk_spl                   false
% 2.19/0.98  --abstr_cl_out                          false
% 2.19/0.98  
% 2.19/0.98  ------ Global Options
% 2.19/0.98  
% 2.19/0.98  --schedule                              default
% 2.19/0.98  --add_important_lit                     false
% 2.19/0.98  --prop_solver_per_cl                    1000
% 2.19/0.98  --min_unsat_core                        false
% 2.19/0.98  --soft_assumptions                      false
% 2.19/0.98  --soft_lemma_size                       3
% 2.19/0.98  --prop_impl_unit_size                   0
% 2.19/0.98  --prop_impl_unit                        []
% 2.19/0.98  --share_sel_clauses                     true
% 2.19/0.98  --reset_solvers                         false
% 2.19/0.98  --bc_imp_inh                            [conj_cone]
% 2.19/0.98  --conj_cone_tolerance                   3.
% 2.19/0.98  --extra_neg_conj                        none
% 2.19/0.98  --large_theory_mode                     true
% 2.19/0.98  --prolific_symb_bound                   200
% 2.19/0.98  --lt_threshold                          2000
% 2.19/0.98  --clause_weak_htbl                      true
% 2.19/0.98  --gc_record_bc_elim                     false
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing Options
% 2.19/0.98  
% 2.19/0.98  --preprocessing_flag                    true
% 2.19/0.98  --time_out_prep_mult                    0.1
% 2.19/0.98  --splitting_mode                        input
% 2.19/0.98  --splitting_grd                         true
% 2.19/0.98  --splitting_cvd                         false
% 2.19/0.98  --splitting_cvd_svl                     false
% 2.19/0.98  --splitting_nvd                         32
% 2.19/0.98  --sub_typing                            true
% 2.19/0.98  --prep_gs_sim                           true
% 2.19/0.98  --prep_unflatten                        true
% 2.19/0.98  --prep_res_sim                          true
% 2.19/0.98  --prep_upred                            true
% 2.19/0.98  --prep_sem_filter                       exhaustive
% 2.19/0.98  --prep_sem_filter_out                   false
% 2.19/0.98  --pred_elim                             true
% 2.19/0.98  --res_sim_input                         true
% 2.19/0.98  --eq_ax_congr_red                       true
% 2.19/0.98  --pure_diseq_elim                       true
% 2.19/0.98  --brand_transform                       false
% 2.19/0.98  --non_eq_to_eq                          false
% 2.19/0.98  --prep_def_merge                        true
% 2.19/0.98  --prep_def_merge_prop_impl              false
% 2.19/0.98  --prep_def_merge_mbd                    true
% 2.19/0.98  --prep_def_merge_tr_red                 false
% 2.19/0.98  --prep_def_merge_tr_cl                  false
% 2.19/0.98  --smt_preprocessing                     true
% 2.19/0.98  --smt_ac_axioms                         fast
% 2.19/0.98  --preprocessed_out                      false
% 2.19/0.98  --preprocessed_stats                    false
% 2.19/0.98  
% 2.19/0.98  ------ Abstraction refinement Options
% 2.19/0.98  
% 2.19/0.98  --abstr_ref                             []
% 2.19/0.98  --abstr_ref_prep                        false
% 2.19/0.98  --abstr_ref_until_sat                   false
% 2.19/0.98  --abstr_ref_sig_restrict                funpre
% 2.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.98  --abstr_ref_under                       []
% 2.19/0.98  
% 2.19/0.98  ------ SAT Options
% 2.19/0.98  
% 2.19/0.98  --sat_mode                              false
% 2.19/0.98  --sat_fm_restart_options                ""
% 2.19/0.98  --sat_gr_def                            false
% 2.19/0.98  --sat_epr_types                         true
% 2.19/0.98  --sat_non_cyclic_types                  false
% 2.19/0.98  --sat_finite_models                     false
% 2.19/0.98  --sat_fm_lemmas                         false
% 2.19/0.98  --sat_fm_prep                           false
% 2.19/0.98  --sat_fm_uc_incr                        true
% 2.19/0.98  --sat_out_model                         small
% 2.19/0.98  --sat_out_clauses                       false
% 2.19/0.98  
% 2.19/0.98  ------ QBF Options
% 2.19/0.98  
% 2.19/0.98  --qbf_mode                              false
% 2.19/0.98  --qbf_elim_univ                         false
% 2.19/0.98  --qbf_dom_inst                          none
% 2.19/0.98  --qbf_dom_pre_inst                      false
% 2.19/0.98  --qbf_sk_in                             false
% 2.19/0.98  --qbf_pred_elim                         true
% 2.19/0.98  --qbf_split                             512
% 2.19/0.98  
% 2.19/0.98  ------ BMC1 Options
% 2.19/0.98  
% 2.19/0.98  --bmc1_incremental                      false
% 2.19/0.98  --bmc1_axioms                           reachable_all
% 2.19/0.98  --bmc1_min_bound                        0
% 2.19/0.98  --bmc1_max_bound                        -1
% 2.19/0.98  --bmc1_max_bound_default                -1
% 2.19/0.98  --bmc1_symbol_reachability              true
% 2.19/0.98  --bmc1_property_lemmas                  false
% 2.19/0.98  --bmc1_k_induction                      false
% 2.19/0.98  --bmc1_non_equiv_states                 false
% 2.19/0.98  --bmc1_deadlock                         false
% 2.19/0.98  --bmc1_ucm                              false
% 2.19/0.98  --bmc1_add_unsat_core                   none
% 2.19/0.98  --bmc1_unsat_core_children              false
% 2.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.98  --bmc1_out_stat                         full
% 2.19/0.98  --bmc1_ground_init                      false
% 2.19/0.98  --bmc1_pre_inst_next_state              false
% 2.19/0.98  --bmc1_pre_inst_state                   false
% 2.19/0.98  --bmc1_pre_inst_reach_state             false
% 2.19/0.98  --bmc1_out_unsat_core                   false
% 2.19/0.98  --bmc1_aig_witness_out                  false
% 2.19/0.98  --bmc1_verbose                          false
% 2.19/0.98  --bmc1_dump_clauses_tptp                false
% 2.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.98  --bmc1_dump_file                        -
% 2.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.98  --bmc1_ucm_extend_mode                  1
% 2.19/0.98  --bmc1_ucm_init_mode                    2
% 2.19/0.98  --bmc1_ucm_cone_mode                    none
% 2.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.98  --bmc1_ucm_relax_model                  4
% 2.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.98  --bmc1_ucm_layered_model                none
% 2.19/0.98  --bmc1_ucm_max_lemma_size               10
% 2.19/0.98  
% 2.19/0.98  ------ AIG Options
% 2.19/0.98  
% 2.19/0.98  --aig_mode                              false
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation Options
% 2.19/0.98  
% 2.19/0.98  --instantiation_flag                    true
% 2.19/0.98  --inst_sos_flag                         false
% 2.19/0.98  --inst_sos_phase                        true
% 2.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel_side                     none
% 2.19/0.98  --inst_solver_per_active                1400
% 2.19/0.98  --inst_solver_calls_frac                1.
% 2.19/0.98  --inst_passive_queue_type               priority_queues
% 2.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.98  --inst_passive_queues_freq              [25;2]
% 2.19/0.98  --inst_dismatching                      true
% 2.19/0.98  --inst_eager_unprocessed_to_passive     true
% 2.19/0.98  --inst_prop_sim_given                   true
% 2.19/0.98  --inst_prop_sim_new                     false
% 2.19/0.98  --inst_subs_new                         false
% 2.19/0.98  --inst_eq_res_simp                      false
% 2.19/0.98  --inst_subs_given                       false
% 2.19/0.98  --inst_orphan_elimination               true
% 2.19/0.98  --inst_learning_loop_flag               true
% 2.19/0.98  --inst_learning_start                   3000
% 2.19/0.98  --inst_learning_factor                  2
% 2.19/0.98  --inst_start_prop_sim_after_learn       3
% 2.19/0.98  --inst_sel_renew                        solver
% 2.19/0.98  --inst_lit_activity_flag                true
% 2.19/0.98  --inst_restr_to_given                   false
% 2.19/0.98  --inst_activity_threshold               500
% 2.19/0.98  --inst_out_proof                        true
% 2.19/0.98  
% 2.19/0.98  ------ Resolution Options
% 2.19/0.98  
% 2.19/0.98  --resolution_flag                       false
% 2.19/0.98  --res_lit_sel                           adaptive
% 2.19/0.98  --res_lit_sel_side                      none
% 2.19/0.98  --res_ordering                          kbo
% 2.19/0.98  --res_to_prop_solver                    active
% 2.19/0.98  --res_prop_simpl_new                    false
% 2.19/0.98  --res_prop_simpl_given                  true
% 2.19/0.98  --res_passive_queue_type                priority_queues
% 2.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.98  --res_passive_queues_freq               [15;5]
% 2.19/0.98  --res_forward_subs                      full
% 2.19/0.98  --res_backward_subs                     full
% 2.19/0.98  --res_forward_subs_resolution           true
% 2.19/0.98  --res_backward_subs_resolution          true
% 2.19/0.98  --res_orphan_elimination                true
% 2.19/0.98  --res_time_limit                        2.
% 2.19/0.98  --res_out_proof                         true
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Options
% 2.19/0.98  
% 2.19/0.98  --superposition_flag                    true
% 2.19/0.98  --sup_passive_queue_type                priority_queues
% 2.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.98  --demod_completeness_check              fast
% 2.19/0.98  --demod_use_ground                      true
% 2.19/0.98  --sup_to_prop_solver                    passive
% 2.19/0.98  --sup_prop_simpl_new                    true
% 2.19/0.98  --sup_prop_simpl_given                  true
% 2.19/0.98  --sup_fun_splitting                     false
% 2.19/0.98  --sup_smt_interval                      50000
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Simplification Setup
% 2.19/0.98  
% 2.19/0.98  --sup_indices_passive                   []
% 2.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_full_bw                           [BwDemod]
% 2.19/0.98  --sup_immed_triv                        [TrivRules]
% 2.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_immed_bw_main                     []
% 2.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  
% 2.19/0.98  ------ Combination Options
% 2.19/0.98  
% 2.19/0.98  --comb_res_mult                         3
% 2.19/0.98  --comb_sup_mult                         2
% 2.19/0.98  --comb_inst_mult                        10
% 2.19/0.98  
% 2.19/0.98  ------ Debug Options
% 2.19/0.98  
% 2.19/0.98  --dbg_backtrace                         false
% 2.19/0.98  --dbg_dump_prop_clauses                 false
% 2.19/0.98  --dbg_dump_prop_clauses_file            -
% 2.19/0.98  --dbg_out_stat                          false
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  ------ Proving...
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  % SZS status Theorem for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  fof(f4,conjecture,(
% 2.19/0.98    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f5,negated_conjecture,(
% 2.19/0.98    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.19/0.98    inference(negated_conjecture,[],[f4])).
% 2.19/0.98  
% 2.19/0.98  fof(f9,plain,(
% 2.19/0.98    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.19/0.98    inference(ennf_transformation,[],[f5])).
% 2.19/0.98  
% 2.19/0.98  fof(f10,plain,(
% 2.19/0.98    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.19/0.98    inference(flattening,[],[f9])).
% 2.19/0.98  
% 2.19/0.98  fof(f19,plain,(
% 2.19/0.98    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k5_mcart_1(sK6,sK7,sK8,sK10) != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & ! [X5] : (! [X6] : (! [X7] : (sK9 = X5 | k3_mcart_1(X5,X6,X7) != sK10 | ~m1_subset_1(X7,sK8)) | ~m1_subset_1(X6,sK7)) | ~m1_subset_1(X5,sK6)) & m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f20,plain,(
% 2.19/0.98    k5_mcart_1(sK6,sK7,sK8,sK10) != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & ! [X5] : (! [X6] : (! [X7] : (sK9 = X5 | k3_mcart_1(X5,X6,X7) != sK10 | ~m1_subset_1(X7,sK8)) | ~m1_subset_1(X6,sK7)) | ~m1_subset_1(X5,sK6)) & m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f10,f19])).
% 2.19/0.98  
% 2.19/0.98  fof(f31,plain,(
% 2.19/0.98    m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))),
% 2.19/0.98    inference(cnf_transformation,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f2,axiom,(
% 2.19/0.98    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f7,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.19/0.98    inference(ennf_transformation,[],[f2])).
% 2.19/0.98  
% 2.19/0.98  fof(f17,plain,(
% 2.19/0.98    ( ! [X4,X5] : (! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(X4,X5,sK5(X0,X1,X2,X3)) = X3 & m1_subset_1(sK5(X0,X1,X2,X3),X2)))) )),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f16,plain,(
% 2.19/0.98    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(X4,sK4(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK4(X0,X1,X2,X3),X1)))) )),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f15,plain,(
% 2.19/0.98    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK3(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK3(X0,X1,X2,X3),X0)))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f18,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3)) = X3 & m1_subset_1(sK5(X0,X1,X2,X3),X2)) & m1_subset_1(sK4(X0,X1,X2,X3),X1)) & m1_subset_1(sK3(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f7,f17,f16,f15])).
% 2.19/0.98  
% 2.19/0.98  fof(f24,plain,(
% 2.19/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.19/0.98    inference(cnf_transformation,[],[f18])).
% 2.19/0.98  
% 2.19/0.98  fof(f1,axiom,(
% 2.19/0.98    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ! [X4] : (m1_subset_1(X4,X0) => (k5_mcart_1(X0,X1,X2,X3) = X4 <=> ! [X5,X6,X7] : (k3_mcart_1(X5,X6,X7) = X3 => X4 = X5)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f6,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((k5_mcart_1(X0,X1,X2,X3) = X4 <=> ! [X5,X6,X7] : (X4 = X5 | k3_mcart_1(X5,X6,X7) != X3)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.19/0.98    inference(ennf_transformation,[],[f1])).
% 2.19/0.98  
% 2.19/0.98  fof(f11,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k5_mcart_1(X0,X1,X2,X3) = X4 | ? [X5,X6,X7] : (X4 != X5 & k3_mcart_1(X5,X6,X7) = X3)) & (! [X5,X6,X7] : (X4 = X5 | k3_mcart_1(X5,X6,X7) != X3) | k5_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.19/0.98    inference(nnf_transformation,[],[f6])).
% 2.19/0.98  
% 2.19/0.98  fof(f12,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k5_mcart_1(X0,X1,X2,X3) = X4 | ? [X5,X6,X7] : (X4 != X5 & k3_mcart_1(X5,X6,X7) = X3)) & (! [X8,X9,X10] : (X4 = X8 | k3_mcart_1(X8,X9,X10) != X3) | k5_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.19/0.98    inference(rectify,[],[f11])).
% 2.19/0.98  
% 2.19/0.98  fof(f13,plain,(
% 2.19/0.98    ! [X4,X3] : (? [X5,X6,X7] : (X4 != X5 & k3_mcart_1(X5,X6,X7) = X3) => (sK0(X3,X4) != X4 & k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f14,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k5_mcart_1(X0,X1,X2,X3) = X4 | (sK0(X3,X4) != X4 & k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3)) & (! [X8,X9,X10] : (X4 = X8 | k3_mcart_1(X8,X9,X10) != X3) | k5_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 2.19/0.98  
% 2.19/0.98  fof(f22,plain,(
% 2.19/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = X4 | k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3 | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.19/0.98    inference(cnf_transformation,[],[f14])).
% 2.19/0.98  
% 2.19/0.98  fof(f33,plain,(
% 2.19/0.98    k1_xboole_0 != sK6),
% 2.19/0.98    inference(cnf_transformation,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f34,plain,(
% 2.19/0.98    k1_xboole_0 != sK7),
% 2.19/0.98    inference(cnf_transformation,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f35,plain,(
% 2.19/0.98    k1_xboole_0 != sK8),
% 2.19/0.98    inference(cnf_transformation,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f27,plain,(
% 2.19/0.98    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.19/0.98    inference(cnf_transformation,[],[f18])).
% 2.19/0.98  
% 2.19/0.98  fof(f3,axiom,(
% 2.19/0.98    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f8,plain,(
% 2.19/0.98    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5))),
% 2.19/0.98    inference(ennf_transformation,[],[f3])).
% 2.19/0.98  
% 2.19/0.98  fof(f30,plain,(
% 2.19/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f8])).
% 2.19/0.98  
% 2.19/0.98  fof(f32,plain,(
% 2.19/0.98    ( ! [X6,X7,X5] : (sK9 = X5 | k3_mcart_1(X5,X6,X7) != sK10 | ~m1_subset_1(X7,sK8) | ~m1_subset_1(X6,sK7) | ~m1_subset_1(X5,sK6)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f26,plain,(
% 2.19/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.19/0.98    inference(cnf_transformation,[],[f18])).
% 2.19/0.98  
% 2.19/0.98  fof(f25,plain,(
% 2.19/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.19/0.98    inference(cnf_transformation,[],[f18])).
% 2.19/0.98  
% 2.19/0.98  fof(f36,plain,(
% 2.19/0.98    k5_mcart_1(sK6,sK7,sK8,sK10) != sK9),
% 2.19/0.98    inference(cnf_transformation,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f28,plain,(
% 2.19/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f8])).
% 2.19/0.98  
% 2.19/0.98  fof(f23,plain,(
% 2.19/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = X4 | sK0(X3,X4) != X4 | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.19/0.98    inference(cnf_transformation,[],[f14])).
% 2.19/0.98  
% 2.19/0.98  cnf(c_15,negated_conjecture,
% 2.19/0.98      ( m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) ),
% 2.19/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_264,plain,
% 2.19/0.98      ( m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_6,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 2.19/0.98      | m1_subset_1(sK3(X1,X2,X3,X0),X1)
% 2.19/0.98      | k1_xboole_0 = X3
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f24]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_266,plain,
% 2.19/0.98      ( k1_xboole_0 = X0
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3(X1,X0,X2,X3),X1) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,X1)
% 2.19/0.98      | ~ m1_subset_1(X2,k3_zfmisc_1(X1,X3,X4))
% 2.19/0.98      | k5_mcart_1(X1,X3,X4,X2) = X0
% 2.19/0.98      | k3_mcart_1(sK0(X2,X0),sK1(X2,X0),sK2(X2,X0)) = X2
% 2.19/0.98      | k1_xboole_0 = X4
% 2.19/0.98      | k1_xboole_0 = X3
% 2.19/0.98      | k1_xboole_0 = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f22]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_271,plain,
% 2.19/0.98      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.19/0.98      | k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3
% 2.19/0.98      | k1_xboole_0 = X0
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | m1_subset_1(X4,X0) != iProver_top
% 2.19/0.98      | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2183,plain,
% 2.19/0.98      ( k5_mcart_1(sK6,sK7,sK8,sK10) = X0
% 2.19/0.98      | k3_mcart_1(sK0(sK10,X0),sK1(sK10,X0),sK2(sK10,X0)) = sK10
% 2.19/0.98      | sK8 = k1_xboole_0
% 2.19/0.98      | sK7 = k1_xboole_0
% 2.19/0.98      | sK6 = k1_xboole_0
% 2.19/0.98      | m1_subset_1(X0,sK6) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_264,c_271]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_13,negated_conjecture,
% 2.19/0.98      ( k1_xboole_0 != sK6 ),
% 2.19/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_12,negated_conjecture,
% 2.19/0.98      ( k1_xboole_0 != sK7 ),
% 2.19/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_11,negated_conjecture,
% 2.19/0.98      ( k1_xboole_0 != sK8 ),
% 2.19/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_113,plain,( X0 = X0 ),theory(equality) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_124,plain,
% 2.19/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_113]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_114,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_406,plain,
% 2.19/0.98      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_114]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_407,plain,
% 2.19/0.98      ( sK8 != k1_xboole_0
% 2.19/0.98      | k1_xboole_0 = sK8
% 2.19/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_406]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_408,plain,
% 2.19/0.98      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_114]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_409,plain,
% 2.19/0.98      ( sK7 != k1_xboole_0
% 2.19/0.98      | k1_xboole_0 = sK7
% 2.19/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_408]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_410,plain,
% 2.19/0.98      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_114]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_411,plain,
% 2.19/0.98      ( sK6 != k1_xboole_0
% 2.19/0.98      | k1_xboole_0 = sK6
% 2.19/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_410]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2266,plain,
% 2.19/0.98      ( k3_mcart_1(sK0(sK10,X0),sK1(sK10,X0),sK2(sK10,X0)) = sK10
% 2.19/0.98      | k5_mcart_1(sK6,sK7,sK8,sK10) = X0
% 2.19/0.98      | m1_subset_1(X0,sK6) != iProver_top ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_2183,c_13,c_12,c_11,c_124,c_407,c_409,c_411]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2267,plain,
% 2.19/0.98      ( k5_mcart_1(sK6,sK7,sK8,sK10) = X0
% 2.19/0.98      | k3_mcart_1(sK0(sK10,X0),sK1(sK10,X0),sK2(sK10,X0)) = sK10
% 2.19/0.98      | m1_subset_1(X0,sK6) != iProver_top ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_2266]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2275,plain,
% 2.19/0.98      ( sK3(sK6,X0,X1,X2) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | k3_mcart_1(sK0(sK10,sK3(sK6,X0,X1,X2)),sK1(sK10,sK3(sK6,X0,X1,X2)),sK2(sK10,sK3(sK6,X0,X1,X2))) = sK10
% 2.19/0.98      | sK6 = k1_xboole_0
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = X0
% 2.19/0.98      | m1_subset_1(X2,k3_zfmisc_1(sK6,X0,X1)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_266,c_2267]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2338,plain,
% 2.19/0.98      ( k3_mcart_1(sK0(sK10,sK3(sK6,X0,X1,X2)),sK1(sK10,sK3(sK6,X0,X1,X2)),sK2(sK10,sK3(sK6,X0,X1,X2))) = sK10
% 2.19/0.98      | sK3(sK6,X0,X1,X2) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = X0
% 2.19/0.98      | m1_subset_1(X2,k3_zfmisc_1(sK6,X0,X1)) != iProver_top ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_2275,c_13,c_124,c_411]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2339,plain,
% 2.19/0.98      ( sK3(sK6,X0,X1,X2) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | k3_mcart_1(sK0(sK10,sK3(sK6,X0,X1,X2)),sK1(sK10,sK3(sK6,X0,X1,X2)),sK2(sK10,sK3(sK6,X0,X1,X2))) = sK10
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = X0
% 2.19/0.98      | m1_subset_1(X2,k3_zfmisc_1(sK6,X0,X1)) != iProver_top ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_2338]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2347,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | k3_mcart_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK2(sK10,sK3(sK6,sK7,sK8,sK10))) = sK10
% 2.19/0.98      | sK8 = k1_xboole_0
% 2.19/0.98      | sK7 = k1_xboole_0 ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_264,c_2339]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2410,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | k3_mcart_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK2(sK10,sK3(sK6,sK7,sK8,sK10))) = sK10 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_2347,c_12,c_11,c_124,c_407,c_409]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 2.19/0.98      | k3_mcart_1(sK3(X1,X2,X3,X0),sK4(X1,X2,X3,X0),sK5(X1,X2,X3,X0)) = X0
% 2.19/0.98      | k1_xboole_0 = X3
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_269,plain,
% 2.19/0.98      ( k3_mcart_1(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3)) = X3
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = X0
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1162,plain,
% 2.19/0.98      ( k3_mcart_1(sK3(sK6,sK7,sK8,sK10),sK4(sK6,sK7,sK8,sK10),sK5(sK6,sK7,sK8,sK10)) = sK10
% 2.19/0.98      | sK8 = k1_xboole_0
% 2.19/0.98      | sK7 = k1_xboole_0
% 2.19/0.98      | sK6 = k1_xboole_0 ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_264,c_269]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1225,plain,
% 2.19/0.98      ( k3_mcart_1(sK3(sK6,sK7,sK8,sK10),sK4(sK6,sK7,sK8,sK10),sK5(sK6,sK7,sK8,sK10)) = sK10 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_1162,c_13,c_12,c_11,c_124,c_407,c_409,c_411]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_7,plain,
% 2.19/0.98      ( X0 = X1 | k3_mcart_1(X2,X3,X0) != k3_mcart_1(X4,X5,X1) ),
% 2.19/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1229,plain,
% 2.19/0.98      ( sK5(sK6,sK7,sK8,sK10) = X0 | k3_mcart_1(X1,X2,X0) != sK10 ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1225,c_7]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2424,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | sK2(sK10,sK3(sK6,sK7,sK8,sK10)) = sK5(sK6,sK7,sK8,sK10) ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_2410,c_1229]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_14,negated_conjecture,
% 2.19/0.98      ( ~ m1_subset_1(X0,sK8)
% 2.19/0.98      | ~ m1_subset_1(X1,sK7)
% 2.19/0.98      | ~ m1_subset_1(X2,sK6)
% 2.19/0.98      | k3_mcart_1(X2,X1,X0) != sK10
% 2.19/0.98      | sK9 = X2 ),
% 2.19/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_265,plain,
% 2.19/0.98      ( k3_mcart_1(X0,X1,X2) != sK10
% 2.19/0.98      | sK9 = X0
% 2.19/0.98      | m1_subset_1(X2,sK8) != iProver_top
% 2.19/0.98      | m1_subset_1(X1,sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(X0,sK6) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2416,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK9
% 2.19/0.98      | m1_subset_1(sK2(sK10,sK3(sK6,sK7,sK8,sK10)),sK8) != iProver_top
% 2.19/0.98      | m1_subset_1(sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK6) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_2410,c_265]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2553,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK9
% 2.19/0.98      | m1_subset_1(sK5(sK6,sK7,sK8,sK10),sK8) != iProver_top
% 2.19/0.98      | m1_subset_1(sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK6) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_2424,c_2416]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_16,plain,
% 2.19/0.98      ( m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_4,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 2.19/0.98      | m1_subset_1(sK5(X1,X2,X3,X0),X3)
% 2.19/0.98      | k1_xboole_0 = X3
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_443,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,sK8))
% 2.19/0.98      | m1_subset_1(sK5(X1,X2,sK8,X0),sK8)
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = sK8 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_659,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK7,sK8))
% 2.19/0.98      | m1_subset_1(sK5(X1,sK7,sK8,X0),sK8)
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = sK8
% 2.19/0.98      | k1_xboole_0 = sK7 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_443]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_967,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(sK6,sK7,sK8))
% 2.19/0.98      | m1_subset_1(sK5(sK6,sK7,sK8,X0),sK8)
% 2.19/0.98      | k1_xboole_0 = sK8
% 2.19/0.98      | k1_xboole_0 = sK7
% 2.19/0.98      | k1_xboole_0 = sK6 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_659]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2317,plain,
% 2.19/0.98      ( m1_subset_1(sK5(sK6,sK7,sK8,sK10),sK8)
% 2.19/0.98      | ~ m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))
% 2.19/0.98      | k1_xboole_0 = sK8
% 2.19/0.98      | k1_xboole_0 = sK7
% 2.19/0.98      | k1_xboole_0 = sK6 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_967]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2318,plain,
% 2.19/0.98      ( k1_xboole_0 = sK8
% 2.19/0.98      | k1_xboole_0 = sK7
% 2.19/0.98      | k1_xboole_0 = sK6
% 2.19/0.98      | m1_subset_1(sK5(sK6,sK7,sK8,sK10),sK8) = iProver_top
% 2.19/0.98      | m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_2317]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3809,plain,
% 2.19/0.98      ( sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK9
% 2.19/0.98      | sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | m1_subset_1(sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK6) != iProver_top ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_2553,c_16,c_13,c_12,c_11,c_2318]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3810,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK9
% 2.19/0.98      | m1_subset_1(sK1(sK10,sK3(sK6,sK7,sK8,sK10)),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK0(sK10,sK3(sK6,sK7,sK8,sK10)),sK6) != iProver_top ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_3809]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_5,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 2.19/0.98      | m1_subset_1(sK4(X1,X2,X3,X0),X2)
% 2.19/0.98      | k1_xboole_0 = X3
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f25]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_267,plain,
% 2.19/0.98      ( k1_xboole_0 = X0
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK4(X1,X0,X2,X3),X0) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_268,plain,
% 2.19/0.98      ( k1_xboole_0 = X0
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
% 2.19/0.98      | m1_subset_1(sK5(X1,X0,X2,X3),X2) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1228,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = sK9
% 2.19/0.98      | m1_subset_1(sK5(sK6,sK7,sK8,sK10),sK8) != iProver_top
% 2.19/0.98      | m1_subset_1(sK4(sK6,sK7,sK8,sK10),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1225,c_265]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1428,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = sK9
% 2.19/0.98      | sK8 = k1_xboole_0
% 2.19/0.98      | sK7 = k1_xboole_0
% 2.19/0.98      | sK6 = k1_xboole_0
% 2.19/0.98      | m1_subset_1(sK4(sK6,sK7,sK8,sK10),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top
% 2.19/0.98      | m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_268,c_1228]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2328,plain,
% 2.19/0.98      ( m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top
% 2.19/0.98      | m1_subset_1(sK4(sK6,sK7,sK8,sK10),sK7) != iProver_top
% 2.19/0.98      | sK3(sK6,sK7,sK8,sK10) = sK9 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_1428,c_16,c_13,c_12,c_11,c_124,c_407,c_409,c_411]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2329,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = sK9
% 2.19/0.98      | m1_subset_1(sK4(sK6,sK7,sK8,sK10),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_2328]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2335,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = sK9
% 2.19/0.98      | sK8 = k1_xboole_0
% 2.19/0.98      | sK7 = k1_xboole_0
% 2.19/0.98      | sK6 = k1_xboole_0
% 2.19/0.98      | m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6) != iProver_top
% 2.19/0.98      | m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_267,c_2329]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2336,plain,
% 2.19/0.98      ( ~ m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6)
% 2.19/0.98      | ~ m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))
% 2.19/0.98      | sK3(sK6,sK7,sK8,sK10) = sK9
% 2.19/0.98      | sK8 = k1_xboole_0
% 2.19/0.98      | sK7 = k1_xboole_0
% 2.19/0.98      | sK6 = k1_xboole_0 ),
% 2.19/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2335]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_461,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,sK8))
% 2.19/0.98      | m1_subset_1(sK3(X1,X2,sK8,X0),X1)
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = sK8 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_734,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK7,sK8))
% 2.19/0.98      | m1_subset_1(sK3(X1,sK7,sK8,X0),X1)
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = sK8
% 2.19/0.98      | k1_xboole_0 = sK7 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_461]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1388,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k3_zfmisc_1(sK6,sK7,sK8))
% 2.19/0.98      | m1_subset_1(sK3(sK6,sK7,sK8,X0),sK6)
% 2.19/0.98      | k1_xboole_0 = sK8
% 2.19/0.98      | k1_xboole_0 = sK7
% 2.19/0.98      | k1_xboole_0 = sK6 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_734]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2698,plain,
% 2.19/0.98      ( m1_subset_1(sK3(sK6,sK7,sK8,sK10),sK6)
% 2.19/0.98      | ~ m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))
% 2.19/0.98      | k1_xboole_0 = sK8
% 2.19/0.98      | k1_xboole_0 = sK7
% 2.19/0.98      | k1_xboole_0 = sK6 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1388]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2702,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = sK9 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_2335,c_15,c_13,c_12,c_11,c_124,c_407,c_409,c_411,
% 2.19/0.98                 c_2336,c_2698]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3813,plain,
% 2.19/0.98      ( k5_mcart_1(sK6,sK7,sK8,sK10) = sK9
% 2.19/0.98      | sK0(sK10,sK9) = sK9
% 2.19/0.98      | m1_subset_1(sK1(sK10,sK9),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK0(sK10,sK9),sK6) != iProver_top ),
% 2.19/0.98      inference(light_normalisation,[status(thm)],[c_3810,c_2702]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_10,negated_conjecture,
% 2.19/0.98      ( k5_mcart_1(sK6,sK7,sK8,sK10) != sK9 ),
% 2.19/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3818,plain,
% 2.19/0.98      ( sK0(sK10,sK9) = sK9
% 2.19/0.98      | m1_subset_1(sK1(sK10,sK9),sK7) != iProver_top
% 2.19/0.98      | m1_subset_1(sK0(sK10,sK9),sK6) != iProver_top ),
% 2.19/0.98      inference(forward_subsumption_resolution,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_3813,c_10]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_9,plain,
% 2.19/0.98      ( X0 = X1 | k3_mcart_1(X0,X2,X3) != k3_mcart_1(X1,X4,X5) ),
% 2.19/0.98      inference(cnf_transformation,[],[f28]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1233,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = X0 | k3_mcart_1(X0,X1,X2) != sK10 ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1225,c_9]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2415,plain,
% 2.19/0.98      ( sK3(sK6,sK7,sK8,sK10) = k5_mcart_1(sK6,sK7,sK8,sK10)
% 2.19/0.98      | sK0(sK10,sK3(sK6,sK7,sK8,sK10)) = sK3(sK6,sK7,sK8,sK10) ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_2410,c_1233]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2710,plain,
% 2.19/0.98      ( k5_mcart_1(sK6,sK7,sK8,sK10) = sK9 | sK0(sK10,sK9) = sK9 ),
% 2.19/0.98      inference(demodulation,[status(thm)],[c_2702,c_2415]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3820,plain,
% 2.19/0.98      ( sK0(sK10,sK9) = sK9 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_3818,c_10,c_2710]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_0,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,X1)
% 2.19/0.98      | ~ m1_subset_1(X2,k3_zfmisc_1(X1,X3,X4))
% 2.19/0.98      | k5_mcart_1(X1,X3,X4,X2) = X0
% 2.19/0.98      | sK0(X2,X0) != X0
% 2.19/0.98      | k1_xboole_0 = X4
% 2.19/0.98      | k1_xboole_0 = X3
% 2.19/0.98      | k1_xboole_0 = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f23]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_272,plain,
% 2.19/0.98      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.19/0.98      | sK0(X3,X4) != X4
% 2.19/0.98      | k1_xboole_0 = X0
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | m1_subset_1(X4,X0) != iProver_top
% 2.19/0.98      | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3829,plain,
% 2.19/0.98      ( k5_mcart_1(X0,X1,X2,sK10) = sK9
% 2.19/0.98      | k1_xboole_0 = X2
% 2.19/0.98      | k1_xboole_0 = X1
% 2.19/0.98      | k1_xboole_0 = X0
% 2.19/0.98      | m1_subset_1(sK9,X0) != iProver_top
% 2.19/0.98      | m1_subset_1(sK10,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_3820,c_272]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_4146,plain,
% 2.19/0.98      ( k5_mcart_1(sK6,sK7,sK8,sK10) = sK9
% 2.19/0.98      | sK8 = k1_xboole_0
% 2.19/0.98      | sK7 = k1_xboole_0
% 2.19/0.98      | sK6 = k1_xboole_0
% 2.19/0.98      | m1_subset_1(sK9,sK6) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_264,c_3829]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2783,plain,
% 2.19/0.98      ( sK8 = k1_xboole_0
% 2.19/0.98      | sK7 = k1_xboole_0
% 2.19/0.98      | sK6 = k1_xboole_0
% 2.19/0.98      | m1_subset_1(sK9,sK6) = iProver_top
% 2.19/0.98      | m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_2702,c_266]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(contradiction,plain,
% 2.19/0.98      ( $false ),
% 2.19/0.98      inference(minisat,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_4146,c_2783,c_411,c_409,c_407,c_124,c_10,c_11,c_12,
% 2.19/0.98                 c_13,c_16]) ).
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  ------                               Statistics
% 2.19/0.98  
% 2.19/0.98  ------ General
% 2.19/0.98  
% 2.19/0.98  abstr_ref_over_cycles:                  0
% 2.19/0.98  abstr_ref_under_cycles:                 0
% 2.19/0.98  gc_basic_clause_elim:                   0
% 2.19/0.98  forced_gc_time:                         0
% 2.19/0.98  parsing_time:                           0.009
% 2.19/0.98  unif_index_cands_time:                  0.
% 2.19/0.98  unif_index_add_time:                    0.
% 2.19/0.98  orderings_time:                         0.
% 2.19/0.98  out_proof_time:                         0.008
% 2.19/0.98  total_time:                             0.191
% 2.19/0.98  num_of_symbols:                         47
% 2.19/0.98  num_of_terms:                           8884
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing
% 2.19/0.98  
% 2.19/0.98  num_of_splits:                          0
% 2.19/0.98  num_of_split_atoms:                     0
% 2.19/0.98  num_of_reused_defs:                     0
% 2.19/0.98  num_eq_ax_congr_red:                    36
% 2.19/0.98  num_of_sem_filtered_clauses:            1
% 2.19/0.98  num_of_subtypes:                        0
% 2.19/0.98  monotx_restored_types:                  0
% 2.19/0.98  sat_num_of_epr_types:                   0
% 2.19/0.98  sat_num_of_non_cyclic_types:            0
% 2.19/0.98  sat_guarded_non_collapsed_types:        0
% 2.19/0.98  num_pure_diseq_elim:                    0
% 2.19/0.98  simp_replaced_by:                       0
% 2.19/0.98  res_preprocessed:                       61
% 2.19/0.98  prep_upred:                             0
% 2.19/0.98  prep_unflattend:                        0
% 2.19/0.98  smt_new_axioms:                         0
% 2.19/0.98  pred_elim_cands:                        1
% 2.19/0.98  pred_elim:                              0
% 2.19/0.98  pred_elim_cl:                           0
% 2.19/0.98  pred_elim_cycles:                       1
% 2.19/0.98  merged_defs:                            0
% 2.19/0.98  merged_defs_ncl:                        0
% 2.19/0.98  bin_hyper_res:                          0
% 2.19/0.98  prep_cycles:                            3
% 2.19/0.98  pred_elim_time:                         0.
% 2.19/0.98  splitting_time:                         0.
% 2.19/0.98  sem_filter_time:                        0.
% 2.19/0.98  monotx_time:                            0.
% 2.19/0.98  subtype_inf_time:                       0.
% 2.19/0.98  
% 2.19/0.98  ------ Problem properties
% 2.19/0.98  
% 2.19/0.98  clauses:                                16
% 2.19/0.98  conjectures:                            6
% 2.19/0.98  epr:                                    3
% 2.19/0.98  horn:                                   9
% 2.19/0.98  ground:                                 5
% 2.19/0.98  unary:                                  5
% 2.19/0.98  binary:                                 3
% 2.19/0.98  lits:                                   56
% 2.19/0.98  lits_eq:                                39
% 2.19/0.98  fd_pure:                                0
% 2.19/0.98  fd_pseudo:                              0
% 2.19/0.98  fd_cond:                                4
% 2.19/0.98  fd_pseudo_cond:                         4
% 2.19/0.98  ac_symbols:                             0
% 2.19/0.98  
% 2.19/0.98  ------ Propositional Solver
% 2.19/0.98  
% 2.19/0.98  prop_solver_calls:                      23
% 2.19/0.98  prop_fast_solver_calls:                 641
% 2.19/0.98  smt_solver_calls:                       0
% 2.19/0.98  smt_fast_solver_calls:                  0
% 2.19/0.98  prop_num_of_clauses:                    1912
% 2.19/0.98  prop_preprocess_simplified:             4947
% 2.19/0.98  prop_fo_subsumed:                       24
% 2.19/0.98  prop_solver_time:                       0.
% 2.19/0.98  smt_solver_time:                        0.
% 2.19/0.98  smt_fast_solver_time:                   0.
% 2.19/0.98  prop_fast_solver_time:                  0.
% 2.19/0.98  prop_unsat_core_time:                   0.
% 2.19/0.98  
% 2.19/0.98  ------ QBF
% 2.19/0.98  
% 2.19/0.98  qbf_q_res:                              0
% 2.19/0.98  qbf_num_tautologies:                    0
% 2.19/0.98  qbf_prep_cycles:                        0
% 2.19/0.98  
% 2.19/0.98  ------ BMC1
% 2.19/0.98  
% 2.19/0.98  bmc1_current_bound:                     -1
% 2.19/0.98  bmc1_last_solved_bound:                 -1
% 2.19/0.98  bmc1_unsat_core_size:                   -1
% 2.19/0.98  bmc1_unsat_core_parents_size:           -1
% 2.19/0.98  bmc1_merge_next_fun:                    0
% 2.19/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation
% 2.19/0.98  
% 2.19/0.98  inst_num_of_clauses:                    630
% 2.19/0.98  inst_num_in_passive:                    163
% 2.19/0.98  inst_num_in_active:                     250
% 2.19/0.98  inst_num_in_unprocessed:                217
% 2.19/0.98  inst_num_of_loops:                      250
% 2.19/0.98  inst_num_of_learning_restarts:          0
% 2.19/0.98  inst_num_moves_active_passive:          0
% 2.19/0.98  inst_lit_activity:                      0
% 2.19/0.98  inst_lit_activity_moves:                0
% 2.19/0.98  inst_num_tautologies:                   0
% 2.19/0.98  inst_num_prop_implied:                  0
% 2.19/0.98  inst_num_existing_simplified:           0
% 2.19/0.98  inst_num_eq_res_simplified:             0
% 2.19/0.98  inst_num_child_elim:                    0
% 2.19/0.98  inst_num_of_dismatching_blockings:      8
% 2.19/0.98  inst_num_of_non_proper_insts:           421
% 2.19/0.98  inst_num_of_duplicates:                 0
% 2.19/0.98  inst_inst_num_from_inst_to_res:         0
% 2.19/0.98  inst_dismatching_checking_time:         0.
% 2.19/0.98  
% 2.19/0.98  ------ Resolution
% 2.19/0.98  
% 2.19/0.98  res_num_of_clauses:                     0
% 2.19/0.98  res_num_in_passive:                     0
% 2.19/0.98  res_num_in_active:                      0
% 2.19/0.98  res_num_of_loops:                       64
% 2.19/0.98  res_forward_subset_subsumed:            32
% 2.19/0.98  res_backward_subset_subsumed:           0
% 2.19/0.98  res_forward_subsumed:                   0
% 2.19/0.98  res_backward_subsumed:                  0
% 2.19/0.98  res_forward_subsumption_resolution:     0
% 2.19/0.98  res_backward_subsumption_resolution:    0
% 2.19/0.98  res_clause_to_clause_subsumption:       245
% 2.19/0.98  res_orphan_elimination:                 0
% 2.19/0.98  res_tautology_del:                      9
% 2.19/0.98  res_num_eq_res_simplified:              0
% 2.19/0.98  res_num_sel_changes:                    0
% 2.19/0.98  res_moves_from_active_to_pass:          0
% 2.19/0.98  
% 2.19/0.98  ------ Superposition
% 2.19/0.98  
% 2.19/0.98  sup_time_total:                         0.
% 2.19/0.98  sup_time_generating:                    0.
% 2.19/0.98  sup_time_sim_full:                      0.
% 2.19/0.98  sup_time_sim_immed:                     0.
% 2.19/0.98  
% 2.19/0.98  sup_num_of_clauses:                     68
% 2.19/0.98  sup_num_in_active:                      30
% 2.19/0.98  sup_num_in_passive:                     38
% 2.19/0.98  sup_num_of_loops:                       48
% 2.19/0.98  sup_fw_superposition:                   44
% 2.19/0.98  sup_bw_superposition:                   81
% 2.19/0.98  sup_immediate_simplified:               8
% 2.19/0.98  sup_given_eliminated:                   0
% 2.19/0.98  comparisons_done:                       0
% 2.19/0.98  comparisons_avoided:                    71
% 2.19/0.98  
% 2.19/0.98  ------ Simplifications
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  sim_fw_subset_subsumed:                 0
% 2.19/0.98  sim_bw_subset_subsumed:                 6
% 2.19/0.98  sim_fw_subsumed:                        0
% 2.19/0.98  sim_bw_subsumed:                        0
% 2.19/0.98  sim_fw_subsumption_res:                 4
% 2.19/0.98  sim_bw_subsumption_res:                 0
% 2.19/0.98  sim_tautology_del:                      0
% 2.19/0.98  sim_eq_tautology_del:                   11
% 2.19/0.98  sim_eq_res_simp:                        0
% 2.19/0.98  sim_fw_demodulated:                     1
% 2.19/0.98  sim_bw_demodulated:                     16
% 2.19/0.98  sim_light_normalised:                   12
% 2.19/0.98  sim_joinable_taut:                      0
% 2.19/0.98  sim_joinable_simp:                      0
% 2.19/0.98  sim_ac_normalised:                      0
% 2.19/0.98  sim_smt_subsumption:                    0
% 2.19/0.98  
%------------------------------------------------------------------------------
