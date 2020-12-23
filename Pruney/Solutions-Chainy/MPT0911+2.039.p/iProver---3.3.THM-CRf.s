%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:08 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  134 (4023 expanded)
%              Number of clauses        :   80 (1393 expanded)
%              Number of leaves         :   13 (1083 expanded)
%              Depth                    :   29
%              Number of atoms          :  622 (25850 expanded)
%              Number of equality atoms :  505 (17191 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X7
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X7
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f16,f21])).

fof(f39,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f39,f24])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( X3 != X5
                  & k3_mcart_1(X5,X6,X7) = X4
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( X3 != X5
                  & k3_mcart_1(X5,X6,X7) = X4
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f19,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( X3 != X5
          & k3_mcart_1(X5,X6,X7) = X4
          & m1_subset_1(X7,X2) )
     => ( X3 != X5
        & k3_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( X3 != X5
              & k3_mcart_1(X5,X6,X7) = X4
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( X3 != X5
            & k3_mcart_1(X5,sK1(X0,X1,X2,X3,X4),X7) = X4
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( X3 != X5
                  & k3_mcart_1(X5,X6,X7) = X4
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( sK0(X0,X1,X2,X3,X4) != X3
                & k3_mcart_1(sK0(X0,X1,X2,X3,X4),X6,X7) = X4
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ( sK0(X0,X1,X2,X3,X4) != X3
        & k3_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) )
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f19,f18,f17])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f37,f23,f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f41,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f11])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f32,f23,f24])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f44,plain,(
    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k3_mcart_1(X4,X5,X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f33,f23,f24])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X6
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f34,f24])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f35,f24])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f36,f24])).

fof(f40,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f40,f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X3
            & k6_mcart_1(X0,X1,X2,X3) != X3
            & k5_mcart_1(X0,X1,X2,X3) != X3 )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) != X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f24])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_447,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = X4
    | k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0)),sK2(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_452,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k4_tarski(k4_tarski(sK0(X0,X1,X2,X4,X3),sK1(X0,X1,X2,X4,X3)),sK2(X0,X1,X2,X4,X3)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2317,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = X0
    | k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_452])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_460,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1361,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_460])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_190,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_209,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_191,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_668,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_669,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_670,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_671,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_672,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_673,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1766,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1361,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_2386,plain,
    ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2317,c_1766])).

cnf(c_2396,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0
    | k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2386,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_2397,plain,
    ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(renaming,[status(thm)],[c_2396])).

cnf(c_7,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
    | k6_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X1
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_455,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2407,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X3,sK7),sK1(sK3,sK4,sK5,X3,sK7)),sK2(sK3,sK4,sK5,X3,sK7))) = sK1(sK3,sK4,sK5,X3,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2397,c_455])).

cnf(c_2804,plain,
    ( k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK1(sK3,sK4,sK5,X0,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_2407])).

cnf(c_2806,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0
    | k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK1(sK3,sK4,sK5,X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2804,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_2807,plain,
    ( k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK1(sK3,sK4,sK5,X0,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(renaming,[status(thm)],[c_2806])).

cnf(c_2811,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = k6_mcart_1(sK3,sK4,sK5,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(superposition,[status(thm)],[c_2397,c_2807])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_461,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1566,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_461])).

cnf(c_1935,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1566,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_2832,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2811,c_1935])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_462,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1326,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_462])).

cnf(c_1595,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1326,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_14,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1598,plain,
    ( k2_mcart_1(sK7) != sK6 ),
    inference(demodulation,[status(thm)],[c_1595,c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
    | k7_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X2
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_456,plain,
    ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X5
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2406,plain,
    ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X3,sK7),sK1(sK3,sK4,sK5,X3,sK7)),sK2(sK3,sK4,sK5,X3,sK7))) = sK2(sK3,sK4,sK5,X3,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2397,c_456])).

cnf(c_2761,plain,
    ( k7_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK2(sK3,sK4,sK5,X0,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_2406])).

cnf(c_2763,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0
    | k7_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK2(sK3,sK4,sK5,X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2761,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_2764,plain,
    ( k7_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK2(sK3,sK4,sK5,X0,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(renaming,[status(thm)],[c_2763])).

cnf(c_2768,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = k7_mcart_1(sK3,sK4,sK5,sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(superposition,[status(thm)],[c_2397,c_2764])).

cnf(c_2789,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = k2_mcart_1(sK7)
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2768,c_1595])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(sK0(X1,X2,X3,X4,X0),X1)
    | k5_mcart_1(X1,X2,X3,X0) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_449,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2,X4,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(sK1(X1,X2,X3,X4,X0),X2)
    | k5_mcart_1(X1,X2,X3,X0) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_450,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X4,X3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(sK2(X1,X2,X3,X4,X0),X3)
    | k5_mcart_1(X1,X2,X3,X0) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_451,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2,X4,X3),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(X1,sK4)
    | ~ m1_subset_1(X2,sK3)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK7
    | sK6 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_448,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
    | sK6 = X2
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2402,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | m1_subset_1(sK2(sK3,sK4,sK5,X0,sK7),sK5) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2397,c_448])).

cnf(c_2521,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_2402])).

cnf(c_2522,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2521,c_1766])).

cnf(c_20,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2537,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2522,c_20,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_2538,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2537])).

cnf(c_2547,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_2538])).

cnf(c_2548,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2547,c_1766])).

cnf(c_2553,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2548,c_20,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_2554,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2553])).

cnf(c_2562,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_2554])).

cnf(c_2563,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2562,c_1766])).

cnf(c_2590,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2563,c_20,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_2846,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0
    | k2_mcart_1(sK7) = sK6 ),
    inference(superposition,[status(thm)],[c_2789,c_2590])).

cnf(c_2885,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2832,c_1598,c_2846])).

cnf(c_3084,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_2885,c_2885])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) != X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_457,plain,
    ( k5_mcart_1(X0,X1,X2,X3) != X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1769,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) != sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_457])).

cnf(c_2097,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1769,c_20,c_17,c_16,c_15,c_209,c_669,c_671,c_673])).

cnf(c_3086,plain,
    ( sK7 != X0 ),
    inference(superposition,[status(thm)],[c_2885,c_2097])).

cnf(c_3095,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3084,c_3086])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:58:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.59/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.99  
% 2.59/0.99  ------  iProver source info
% 2.59/0.99  
% 2.59/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.99  git: non_committed_changes: false
% 2.59/0.99  git: last_make_outside_of_git: false
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     num_symb
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       true
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  ------ Parsing...
% 2.59/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.99  ------ Proving...
% 2.59/0.99  ------ Problem Properties 
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  clauses                                 20
% 2.59/0.99  conjectures                             6
% 2.59/0.99  EPR                                     3
% 2.59/0.99  Horn                                    6
% 2.59/0.99  unary                                   5
% 2.59/0.99  binary                                  0
% 2.59/0.99  lits                                    85
% 2.59/0.99  lits eq                                 64
% 2.59/0.99  fd_pure                                 0
% 2.59/0.99  fd_pseudo                               0
% 2.59/0.99  fd_cond                                 7
% 2.59/0.99  fd_pseudo_cond                          4
% 2.59/0.99  AC symbols                              0
% 2.59/0.99  
% 2.59/0.99  ------ Schedule dynamic 5 is on 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  Current options:
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     none
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       false
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ Proving...
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  % SZS status Theorem for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99   Resolution empty clause
% 2.59/0.99  
% 2.59/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  fof(f7,conjecture,(
% 2.59/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f8,negated_conjecture,(
% 2.59/0.99    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.59/0.99    inference(negated_conjecture,[],[f7])).
% 2.59/0.99  
% 2.59/0.99  fof(f15,plain,(
% 2.59/0.99    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.59/0.99    inference(ennf_transformation,[],[f8])).
% 2.59/0.99  
% 2.59/0.99  fof(f16,plain,(
% 2.59/0.99    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.59/0.99    inference(flattening,[],[f15])).
% 2.59/0.99  
% 2.59/0.99  fof(f21,plain,(
% 2.59/0.99    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f22,plain,(
% 2.59/0.99    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f16,f21])).
% 2.59/0.99  
% 2.59/0.99  fof(f39,plain,(
% 2.59/0.99    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.59/0.99    inference(cnf_transformation,[],[f22])).
% 2.59/0.99  
% 2.59/0.99  fof(f2,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f24,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f2])).
% 2.59/0.99  
% 2.59/0.99  fof(f60,plain,(
% 2.59/0.99    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.59/0.99    inference(definition_unfolding,[],[f39,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f6,axiom,(
% 2.59/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f13,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X5] : (? [X6] : (? [X7] : ((X3 != X5 & k3_mcart_1(X5,X6,X7) = X4) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0))) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.59/0.99    inference(ennf_transformation,[],[f6])).
% 2.59/0.99  
% 2.59/0.99  fof(f14,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X5] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.59/0.99    inference(flattening,[],[f13])).
% 2.59/0.99  
% 2.59/0.99  fof(f19,plain,(
% 2.59/0.99    ( ! [X6,X5] : (! [X4,X3,X2,X1,X0] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) => (X3 != X5 & k3_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)))) )),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f18,plain,(
% 2.59/0.99    ( ! [X5] : (! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (X3 != X5 & k3_mcart_1(X5,sK1(X0,X1,X2,X3,X4),X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)))) )),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f17,plain,(
% 2.59/0.99    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (sK0(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK0(X0,X1,X2,X3,X4),X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f20,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | (((sK0(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f19,f18,f17])).
% 2.59/0.99  
% 2.59/0.99  fof(f37,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f1,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f23,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f1])).
% 2.59/0.99  
% 2.59/0.99  fof(f55,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f37,f23,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f3,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f9,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.59/0.99    inference(ennf_transformation,[],[f3])).
% 2.59/0.99  
% 2.59/0.99  fof(f25,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(cnf_transformation,[],[f9])).
% 2.59/0.99  
% 2.59/0.99  fof(f47,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(definition_unfolding,[],[f25,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f41,plain,(
% 2.59/0.99    k1_xboole_0 != sK3),
% 2.59/0.99    inference(cnf_transformation,[],[f22])).
% 2.59/0.99  
% 2.59/0.99  fof(f42,plain,(
% 2.59/0.99    k1_xboole_0 != sK4),
% 2.59/0.99    inference(cnf_transformation,[],[f22])).
% 2.59/0.99  
% 2.59/0.99  fof(f43,plain,(
% 2.59/0.99    k1_xboole_0 != sK5),
% 2.59/0.99    inference(cnf_transformation,[],[f22])).
% 2.59/0.99  
% 2.59/0.99  fof(f5,axiom,(
% 2.59/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f11,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.59/0.99    inference(ennf_transformation,[],[f5])).
% 2.59/0.99  
% 2.59/0.99  fof(f12,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.59/0.99    inference(flattening,[],[f11])).
% 2.59/0.99  
% 2.59/0.99  fof(f32,plain,(
% 2.59/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k3_mcart_1(X4,X5,X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f12])).
% 2.59/0.99  
% 2.59/0.99  fof(f52,plain,(
% 2.59/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f32,f23,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f62,plain,(
% 2.59/0.99    ( ! [X6,X4,X2,X0,X5,X1] : (k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.59/0.99    inference(equality_resolution,[],[f52])).
% 2.59/0.99  
% 2.59/0.99  fof(f26,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(cnf_transformation,[],[f9])).
% 2.59/0.99  
% 2.59/0.99  fof(f46,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(definition_unfolding,[],[f26,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f27,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(cnf_transformation,[],[f9])).
% 2.59/0.99  
% 2.59/0.99  fof(f45,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(definition_unfolding,[],[f27,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f44,plain,(
% 2.59/0.99    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6),
% 2.59/0.99    inference(cnf_transformation,[],[f22])).
% 2.59/0.99  
% 2.59/0.99  fof(f33,plain,(
% 2.59/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = X6 | k3_mcart_1(X4,X5,X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f12])).
% 2.59/0.99  
% 2.59/0.99  fof(f51,plain,(
% 2.59/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = X6 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f33,f23,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f61,plain,(
% 2.59/0.99    ( ! [X6,X4,X2,X0,X5,X1] : (k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X6 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.59/0.99    inference(equality_resolution,[],[f51])).
% 2.59/0.99  
% 2.59/0.99  fof(f34,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f58,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f34,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f35,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f57,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f35,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f36,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f56,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f36,f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f40,plain,(
% 2.59/0.99    ( ! [X6,X7,X5] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f22])).
% 2.59/0.99  
% 2.59/0.99  fof(f59,plain,(
% 2.59/0.99    ( ! [X6,X7,X5] : (sK6 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.59/0.99    inference(definition_unfolding,[],[f40,f23])).
% 2.59/0.99  
% 2.59/0.99  fof(f4,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f10,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.59/0.99    inference(ennf_transformation,[],[f4])).
% 2.59/0.99  
% 2.59/0.99  fof(f28,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(cnf_transformation,[],[f10])).
% 2.59/0.99  
% 2.59/0.99  fof(f50,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) != X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(definition_unfolding,[],[f28,f24])).
% 2.59/0.99  
% 2.59/0.99  cnf(c_19,negated_conjecture,
% 2.59/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 2.59/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_447,plain,
% 2.59/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_10,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.59/0.99      | k5_mcart_1(X1,X2,X3,X0) = X4
% 2.59/0.99      | k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0)),sK2(X1,X2,X3,X4,X0)) = X0
% 2.59/0.99      | k1_xboole_0 = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_452,plain,
% 2.59/0.99      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.59/0.99      | k4_tarski(k4_tarski(sK0(X0,X1,X2,X4,X3),sK1(X0,X1,X2,X4,X3)),sK2(X0,X1,X2,X4,X3)) = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2317,plain,
% 2.59/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK7) = X0
% 2.59/0.99      | k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_447,c_452]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.59/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.59/0.99      | k1_xboole_0 = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_460,plain,
% 2.59/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1361,plain,
% 2.59/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_447,c_460]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_17,negated_conjecture,
% 2.59/0.99      ( k1_xboole_0 != sK3 ),
% 2.59/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_16,negated_conjecture,
% 2.59/0.99      ( k1_xboole_0 != sK4 ),
% 2.59/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_15,negated_conjecture,
% 2.59/0.99      ( k1_xboole_0 != sK5 ),
% 2.59/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_190,plain,( X0 = X0 ),theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_209,plain,
% 2.59/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_190]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_191,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_668,plain,
% 2.59/0.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_191]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_669,plain,
% 2.59/0.99      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_668]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_670,plain,
% 2.59/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_191]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_671,plain,
% 2.59/0.99      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_670]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_672,plain,
% 2.59/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_191]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_673,plain,
% 2.59/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_672]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1766,plain,
% 2.59/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1361,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2386,plain,
% 2.59/0.99      ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_2317,c_1766]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2396,plain,
% 2.59/0.99      ( k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2386,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2397,plain,
% 2.59/0.99      ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_2396]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_7,plain,
% 2.59/0.99      ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
% 2.59/0.99      | k6_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X1
% 2.59/0.99      | k1_xboole_0 = X5
% 2.59/0.99      | k1_xboole_0 = X4
% 2.59/0.99      | k1_xboole_0 = X3 ),
% 2.59/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_455,plain,
% 2.59/0.99      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2407,plain,
% 2.59/0.99      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X3,sK7),sK1(sK3,sK4,sK5,X3,sK7)),sK2(sK3,sK4,sK5,X3,sK7))) = sK1(sK3,sK4,sK5,X3,sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2397,c_455]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2804,plain,
% 2.59/0.99      ( k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK1(sK3,sK4,sK5,X0,sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_447,c_2407]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2806,plain,
% 2.59/0.99      ( k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK1(sK3,sK4,sK5,X0,sK7) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2804,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2807,plain,
% 2.59/0.99      ( k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK1(sK3,sK4,sK5,X0,sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_2806]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2811,plain,
% 2.59/0.99      ( sK1(sK3,sK4,sK5,X0,sK7) = k6_mcart_1(sK3,sK4,sK5,sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2397,c_2807]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.59/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.59/0.99      | k1_xboole_0 = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_461,plain,
% 2.59/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1566,plain,
% 2.59/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_447,c_461]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1935,plain,
% 2.59/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1566,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2832,plain,
% 2.59/0.99      ( sK1(sK3,sK4,sK5,X0,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(light_normalisation,[status(thm)],[c_2811,c_1935]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_0,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.59/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.59/0.99      | k1_xboole_0 = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_462,plain,
% 2.59/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1326,plain,
% 2.59/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_447,c_462]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1595,plain,
% 2.59/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1326,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_14,negated_conjecture,
% 2.59/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
% 2.59/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1598,plain,
% 2.59/0.99      ( k2_mcart_1(sK7) != sK6 ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_1595,c_14]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6,plain,
% 2.59/0.99      ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
% 2.59/0.99      | k7_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X2
% 2.59/0.99      | k1_xboole_0 = X5
% 2.59/0.99      | k1_xboole_0 = X4
% 2.59/0.99      | k1_xboole_0 = X3 ),
% 2.59/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_456,plain,
% 2.59/0.99      ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X5
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2406,plain,
% 2.59/0.99      ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X3,sK7),sK1(sK3,sK4,sK5,X3,sK7)),sK2(sK3,sK4,sK5,X3,sK7))) = sK2(sK3,sK4,sK5,X3,sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2397,c_456]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2761,plain,
% 2.59/0.99      ( k7_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK2(sK3,sK4,sK5,X0,sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_447,c_2406]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2763,plain,
% 2.59/0.99      ( k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | k7_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK2(sK3,sK4,sK5,X0,sK7) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2761,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2764,plain,
% 2.59/0.99      ( k7_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7))) = sK2(sK3,sK4,sK5,X0,sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_2763]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2768,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = k7_mcart_1(sK3,sK4,sK5,sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2397,c_2764]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2789,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = k2_mcart_1(sK7)
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(light_normalisation,[status(thm)],[c_2768,c_1595]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_13,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.59/0.99      | m1_subset_1(sK0(X1,X2,X3,X4,X0),X1)
% 2.59/0.99      | k5_mcart_1(X1,X2,X3,X0) = X4
% 2.59/0.99      | k1_xboole_0 = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_449,plain,
% 2.59/0.99      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK0(X0,X1,X2,X4,X3),X0) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_12,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.59/0.99      | m1_subset_1(sK1(X1,X2,X3,X4,X0),X2)
% 2.59/0.99      | k5_mcart_1(X1,X2,X3,X0) = X4
% 2.59/0.99      | k1_xboole_0 = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_450,plain,
% 2.59/0.99      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(X0,X1,X2,X4,X3),X1) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_11,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.59/0.99      | m1_subset_1(sK2(X1,X2,X3,X4,X0),X3)
% 2.59/0.99      | k5_mcart_1(X1,X2,X3,X0) = X4
% 2.59/0.99      | k1_xboole_0 = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_451,plain,
% 2.59/0.99      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
% 2.59/0.99      | m1_subset_1(sK2(X0,X1,X2,X4,X3),X2) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_18,negated_conjecture,
% 2.59/0.99      ( ~ m1_subset_1(X0,sK5)
% 2.59/0.99      | ~ m1_subset_1(X1,sK4)
% 2.59/0.99      | ~ m1_subset_1(X2,sK3)
% 2.59/0.99      | k4_tarski(k4_tarski(X2,X1),X0) != sK7
% 2.59/0.99      | sK6 = X0 ),
% 2.59/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_448,plain,
% 2.59/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
% 2.59/0.99      | sK6 = X2
% 2.59/0.99      | m1_subset_1(X2,sK5) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,sK4) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,sK3) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2402,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | m1_subset_1(sK2(sK3,sK4,sK5,X0,sK7),sK5) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.59/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2397,c_448]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2521,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0
% 2.59/0.99      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.59/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_451,c_2402]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2522,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0
% 2.59/0.99      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.59/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_2521,c_1766]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_20,plain,
% 2.59/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2537,plain,
% 2.59/0.99      ( m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.59/0.99      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.59/0.99      | sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2522,c_20,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2538,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.59/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_2537]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2547,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0
% 2.59/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_450,c_2538]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2548,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0
% 2.59/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_2547,c_1766]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2553,plain,
% 2.59/0.99      ( m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.59/0.99      | sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2548,c_20,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2554,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_2553]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2562,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_449,c_2554]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2563,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.59/0.99      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_2562,c_1766]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2590,plain,
% 2.59/0.99      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6 | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2563,c_20,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2846,plain,
% 2.59/0.99      ( k1_mcart_1(k1_mcart_1(sK7)) = X0 | k2_mcart_1(sK7) = sK6 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2789,c_2590]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2885,plain,
% 2.59/0.99      ( k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2832,c_1598,c_2846]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3084,plain,
% 2.59/0.99      ( X0 = X1 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2885,c_2885]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.59/0.99      | k5_mcart_1(X1,X2,X3,X0) != X0
% 2.59/0.99      | k1_xboole_0 = X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_457,plain,
% 2.59/0.99      ( k5_mcart_1(X0,X1,X2,X3) != X3
% 2.59/0.99      | k1_xboole_0 = X2
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1769,plain,
% 2.59/0.99      ( k1_mcart_1(k1_mcart_1(sK7)) != sK7
% 2.59/0.99      | sK5 = k1_xboole_0
% 2.59/0.99      | sK4 = k1_xboole_0
% 2.59/0.99      | sK3 = k1_xboole_0
% 2.59/0.99      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_1766,c_457]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2097,plain,
% 2.59/0.99      ( k1_mcart_1(k1_mcart_1(sK7)) != sK7 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_1769,c_20,c_17,c_16,c_15,c_209,c_669,c_671,c_673]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3086,plain,
% 2.59/0.99      ( sK7 != X0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2885,c_2097]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3095,plain,
% 2.59/0.99      ( $false ),
% 2.59/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_3084,c_3086]) ).
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  ------                               Statistics
% 2.59/0.99  
% 2.59/0.99  ------ General
% 2.59/0.99  
% 2.59/0.99  abstr_ref_over_cycles:                  0
% 2.59/0.99  abstr_ref_under_cycles:                 0
% 2.59/0.99  gc_basic_clause_elim:                   0
% 2.59/0.99  forced_gc_time:                         0
% 2.59/0.99  parsing_time:                           0.009
% 2.59/0.99  unif_index_cands_time:                  0.
% 2.59/0.99  unif_index_add_time:                    0.
% 2.59/0.99  orderings_time:                         0.
% 2.59/0.99  out_proof_time:                         0.012
% 2.59/0.99  total_time:                             0.148
% 2.59/0.99  num_of_symbols:                         48
% 2.59/0.99  num_of_terms:                           4000
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing
% 2.59/0.99  
% 2.59/0.99  num_of_splits:                          0
% 2.59/0.99  num_of_split_atoms:                     0
% 2.59/0.99  num_of_reused_defs:                     0
% 2.59/0.99  num_eq_ax_congr_red:                    42
% 2.59/0.99  num_of_sem_filtered_clauses:            1
% 2.59/0.99  num_of_subtypes:                        0
% 2.59/0.99  monotx_restored_types:                  0
% 2.59/0.99  sat_num_of_epr_types:                   0
% 2.59/0.99  sat_num_of_non_cyclic_types:            0
% 2.59/0.99  sat_guarded_non_collapsed_types:        0
% 2.59/0.99  num_pure_diseq_elim:                    0
% 2.59/0.99  simp_replaced_by:                       0
% 2.59/0.99  res_preprocessed:                       81
% 2.59/0.99  prep_upred:                             0
% 2.59/0.99  prep_unflattend:                        0
% 2.59/0.99  smt_new_axioms:                         0
% 2.59/0.99  pred_elim_cands:                        1
% 2.59/0.99  pred_elim:                              0
% 2.59/0.99  pred_elim_cl:                           0
% 2.59/0.99  pred_elim_cycles:                       1
% 2.59/0.99  merged_defs:                            0
% 2.59/0.99  merged_defs_ncl:                        0
% 2.59/0.99  bin_hyper_res:                          0
% 2.59/0.99  prep_cycles:                            3
% 2.59/0.99  pred_elim_time:                         0.
% 2.59/0.99  splitting_time:                         0.
% 2.59/0.99  sem_filter_time:                        0.
% 2.59/0.99  monotx_time:                            0.
% 2.59/0.99  subtype_inf_time:                       0.
% 2.59/0.99  
% 2.59/0.99  ------ Problem properties
% 2.59/0.99  
% 2.59/0.99  clauses:                                20
% 2.59/0.99  conjectures:                            6
% 2.59/0.99  epr:                                    3
% 2.59/0.99  horn:                                   6
% 2.59/0.99  ground:                                 5
% 2.59/0.99  unary:                                  5
% 2.59/0.99  binary:                                 0
% 2.59/0.99  lits:                                   85
% 2.59/0.99  lits_eq:                                64
% 2.59/0.99  fd_pure:                                0
% 2.59/0.99  fd_pseudo:                              0
% 2.59/0.99  fd_cond:                                7
% 2.59/0.99  fd_pseudo_cond:                         4
% 2.59/0.99  ac_symbols:                             0
% 2.59/0.99  
% 2.59/0.99  ------ Propositional Solver
% 2.59/0.99  
% 2.59/0.99  prop_solver_calls:                      21
% 2.59/0.99  prop_fast_solver_calls:                 841
% 2.59/0.99  smt_solver_calls:                       0
% 2.59/0.99  smt_fast_solver_calls:                  0
% 2.59/0.99  prop_num_of_clauses:                    1004
% 2.59/0.99  prop_preprocess_simplified:             4229
% 2.59/0.99  prop_fo_subsumed:                       47
% 2.59/0.99  prop_solver_time:                       0.
% 2.59/0.99  smt_solver_time:                        0.
% 2.59/0.99  smt_fast_solver_time:                   0.
% 2.59/0.99  prop_fast_solver_time:                  0.
% 2.59/0.99  prop_unsat_core_time:                   0.
% 2.59/0.99  
% 2.59/0.99  ------ QBF
% 2.59/0.99  
% 2.59/0.99  qbf_q_res:                              0
% 2.59/0.99  qbf_num_tautologies:                    0
% 2.59/0.99  qbf_prep_cycles:                        0
% 2.59/0.99  
% 2.59/0.99  ------ BMC1
% 2.59/0.99  
% 2.59/0.99  bmc1_current_bound:                     -1
% 2.59/0.99  bmc1_last_solved_bound:                 -1
% 2.59/0.99  bmc1_unsat_core_size:                   -1
% 2.59/0.99  bmc1_unsat_core_parents_size:           -1
% 2.59/0.99  bmc1_merge_next_fun:                    0
% 2.59/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation
% 2.59/0.99  
% 2.59/0.99  inst_num_of_clauses:                    288
% 2.59/0.99  inst_num_in_passive:                    50
% 2.59/0.99  inst_num_in_active:                     210
% 2.59/0.99  inst_num_in_unprocessed:                28
% 2.59/0.99  inst_num_of_loops:                      210
% 2.59/0.99  inst_num_of_learning_restarts:          0
% 2.59/0.99  inst_num_moves_active_passive:          0
% 2.59/0.99  inst_lit_activity:                      0
% 2.59/0.99  inst_lit_activity_moves:                0
% 2.59/0.99  inst_num_tautologies:                   0
% 2.59/0.99  inst_num_prop_implied:                  0
% 2.59/0.99  inst_num_existing_simplified:           0
% 2.59/0.99  inst_num_eq_res_simplified:             0
% 2.59/0.99  inst_num_child_elim:                    0
% 2.59/0.99  inst_num_of_dismatching_blockings:      0
% 2.59/0.99  inst_num_of_non_proper_insts:           248
% 2.59/0.99  inst_num_of_duplicates:                 0
% 2.59/0.99  inst_inst_num_from_inst_to_res:         0
% 2.59/0.99  inst_dismatching_checking_time:         0.
% 2.59/0.99  
% 2.59/0.99  ------ Resolution
% 2.59/0.99  
% 2.59/0.99  res_num_of_clauses:                     0
% 2.59/0.99  res_num_in_passive:                     0
% 2.59/0.99  res_num_in_active:                      0
% 2.59/0.99  res_num_of_loops:                       84
% 2.59/0.99  res_forward_subset_subsumed:            4
% 2.59/0.99  res_backward_subset_subsumed:           0
% 2.59/0.99  res_forward_subsumed:                   0
% 2.59/0.99  res_backward_subsumed:                  0
% 2.59/0.99  res_forward_subsumption_resolution:     0
% 2.59/0.99  res_backward_subsumption_resolution:    0
% 2.59/0.99  res_clause_to_clause_subsumption:       241
% 2.59/0.99  res_orphan_elimination:                 0
% 2.59/0.99  res_tautology_del:                      0
% 2.59/0.99  res_num_eq_res_simplified:              0
% 2.59/0.99  res_num_sel_changes:                    0
% 2.59/0.99  res_moves_from_active_to_pass:          0
% 2.59/0.99  
% 2.59/0.99  ------ Superposition
% 2.59/0.99  
% 2.59/0.99  sup_time_total:                         0.
% 2.59/0.99  sup_time_generating:                    0.
% 2.59/0.99  sup_time_sim_full:                      0.
% 2.59/0.99  sup_time_sim_immed:                     0.
% 2.59/0.99  
% 2.59/0.99  sup_num_of_clauses:                     51
% 2.59/0.99  sup_num_in_active:                      13
% 2.59/0.99  sup_num_in_passive:                     38
% 2.59/0.99  sup_num_of_loops:                       41
% 2.59/0.99  sup_fw_superposition:                   24
% 2.59/0.99  sup_bw_superposition:                   32
% 2.59/0.99  sup_immediate_simplified:               19
% 2.59/0.99  sup_given_eliminated:                   0
% 2.59/0.99  comparisons_done:                       0
% 2.59/0.99  comparisons_avoided:                    58
% 2.59/0.99  
% 2.59/0.99  ------ Simplifications
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  sim_fw_subset_subsumed:                 9
% 2.59/0.99  sim_bw_subset_subsumed:                 6
% 2.59/0.99  sim_fw_subsumed:                        6
% 2.59/0.99  sim_bw_subsumed:                        1
% 2.59/0.99  sim_fw_subsumption_res:                 0
% 2.59/0.99  sim_bw_subsumption_res:                 1
% 2.59/0.99  sim_tautology_del:                      0
% 2.59/0.99  sim_eq_tautology_del:                   0
% 2.59/0.99  sim_eq_res_simp:                        0
% 2.59/0.99  sim_fw_demodulated:                     6
% 2.59/0.99  sim_bw_demodulated:                     25
% 2.59/0.99  sim_light_normalised:                   2
% 2.59/0.99  sim_joinable_taut:                      0
% 2.59/0.99  sim_joinable_simp:                      0
% 2.59/0.99  sim_ac_normalised:                      0
% 2.59/0.99  sim_smt_subsumption:                    0
% 2.59/0.99  
%------------------------------------------------------------------------------
